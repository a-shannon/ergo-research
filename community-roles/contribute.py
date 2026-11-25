"""Produce or check a detached structural role for the fixed N0 history."""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import stat
import subprocess
import sys

KIT = Path(__file__).resolve().parent
PUBLIC = KIT / "public"
ROLES = {
    2: ("tree", "TREE2"),
    4: ("height_daa", "DAA4"),
}
NATIVE = "historical_prefix_proof::full_certificate::"
PUBLIC_PINS = {
    "statement.x": "779b5863e53897ab377ceafd93d2b024027f8ee072f43431866957d0e7039a98",
    "commitment.bin": "e6fe4e4ec2337a2261d19b70aace5b3b225537a5fe4bd592117db989fcf99a59",
}
SOURCE_PIN = "e32413041ecf47efe5b86ecbfe8d88956b760aefa7de26cccf24a4cbf8dabef1"
HELPER_PIN = "9e3698c7208768a479765ff9c1c9c346929301e334e60dddbdb43c934718d6de"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def role_bytes(path):
    with path.open("rb") as stream:
        raw = stream.read(9281)
    require(len(raw) == 9280, "Expected exactly 9,280 proof bytes")
    return raw


def checked_source():
    source = KIT / "source"
    expected = {}
    manifest = KIT / "SOURCE-MANIFEST.tsv"
    inventory = manifest.read_bytes()
    require(hashlib.sha256(inventory).hexdigest() == SOURCE_PIN, "Source inventory differs from the release")
    for line in inventory.decode("utf-8-sig").splitlines():
        name, length, sha = line.split("\t")
        path = source / name
        require(path.resolve().is_relative_to(source) and name not in expected, "Invalid source inventory")
        expected[name] = (int(length), sha.lower())
    found = {}
    for path in source.rglob("*"):
        require(not path.is_symlink() and not path.lstat().st_file_attributes & stat.FILE_ATTRIBUTE_REPARSE_POINT,
                f"Unexpected linked source: {path.name}")
        if path.is_file():
            found[path.relative_to(source).as_posix()] = (path.stat().st_size, digest(path))
    require(found == expected, "Rust source differs from the supplied inventory")
    return source, SOURCE_PIN


def build_api():
    path = KIT / "review_build.py"
    require(digest(path) == HELPER_PIN, "Build helper differs from the release")
    spec = importlib.util.spec_from_file_location("role_build", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def invoke(exe, selector, env, work):
    args = [str(exe), selector, "--exact"]
    names = subprocess.check_output([*args, "--list"], cwd=work, env=env, text=True).splitlines()
    require(names.count(selector + ": test") == 1, "Selector absent in this build")
    p = subprocess.run([*args, "--ignored", "--test-threads=1", "--nocapture"],
                       cwd=work, env=env, capture_output=True, text=True)
    sys.stderr.write(p.stderr)
    sys.stdout.write(p.stdout)
    p.check_returncode()
    require("test result: ok. 1 passed; 0 failed; 0 ignored;" in p.stdout, "Native role check did not run")
    return p.stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("build", "produce", "verify"))
    parser.add_argument("--role", type=int, choices=ROLES)
    parser.add_argument("--work", type=Path, required=True)
    parser.add_argument("--witness", type=Path)
    parser.add_argument("--out", type=Path)
    parser.add_argument("--proof", type=Path)
    parser.add_argument("--offline", action="store_true")
    args = parser.parse_args()
    require(os.name == "nt", "Use a 64-bit Windows build with the Rust MSVC toolchain")
    work = args.work.resolve()
    require(not work.is_relative_to(KIT), "Choose a build directory outside the kit")
    for name, pin in PUBLIC_PINS.items():
        require(digest(PUBLIC / name) == pin, f"Different N0 public input: {name}")
    if args.action != "build":
        require(args.role in ROLES, "Choose role 2 or 4")
    if args.action == "produce":
        require(args.witness and args.out and not args.proof, "Use --witness and --out for production")
        witness = args.witness.resolve(strict=True)
        require(witness.stat().st_size == 1 << 38, "Expected a 256 GiB packed N0 witness")
        out = args.out.resolve()
        require(not out.is_relative_to(witness.parent) and not witness.parent.is_relative_to(out)
                and not out.is_relative_to(KIT), "Use a new output directory separate from the kit and witness folder")
        require(not out.exists(), "Output directory already exists")
    if args.action == "verify":
        require(args.proof and not args.witness and not args.out, "Use --proof for public verification")
        proof = args.proof.resolve(strict=True)
        proof_sha = hashlib.sha256(role_bytes(proof)).hexdigest()
    source, manifest = checked_source()
    api = build_api()
    exe = api.build("N0", source, work, args.offline, manifest)
    if args.action == "build":
        print(exe)
        return
    label, prefix = ROLES[args.role]
    env = api.environment()
    env.update(NIPOPOW_V2_INPUTS=str(PUBLIC), RAYON_NUM_THREADS="2", RUST_TEST_THREADS="1")
    base = f"NIPOPOW_V2_{prefix}_"
    env[base + "COMMITMENT"] = str(PUBLIC / "commitment.bin")
    if args.action == "produce":
        env.update(NIPOPOW_H21_WITNESS=str(witness), NIPOPOW_H21_ROLE_BUDGET_BYTES=str(22 << 30),
                   NIPOPOW_H21_CONTEXT_BYTES=str(3 << 30), NIPOPOW_H21_VISITOR_BYTES=str(512 << 20),
                   NIPOPOW_H21_RESERVE_BYTES=str(2 << 30))
        out.mkdir(parents=True)
        env[base + "OUTPUT_DIR"] = str(out)
        invoke(exe, NATIVE + f"produce_detached_n0_{label}_role", env, work)
        proof = out / f"role-{args.role}.gkr"
        proof_sha = hashlib.sha256(role_bytes(proof)).hexdigest()
    env.pop("NIPOPOW_H21_WITNESS", None)
    env.pop(base + "OUTPUT_DIR", None)
    env[base + "PROOF"] = str(proof)
    env[base + "SHA256"] = proof_sha
    invoke(exe, NATIVE + f"verify_detached_n0_{label}_role", env, work)
    print(json.dumps(dict(snapshot="N0", role=args.role, bytes=9280, sha256=proof_sha,
                          source_manifest_sha256=manifest, public_role_check="passed")))


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        sys.exit(str(error))
