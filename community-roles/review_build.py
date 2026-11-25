"""Build and run the era-bound packet verifier for an Ergo historical snapshot."""
import argparse
from contextlib import contextmanager
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import sys


KIT = Path(__file__).resolve().parent
SELECTOR = "historical_prefix_proof::full_certificate::full_cold_client::cold_sync_from_exported_packets"
TIP_ID = "20ed709e5e9ba0d40fa941b2de53a3cdbd5bf29950b4a40adad8d244209ff9b3"
TIP_WORK = "2746808805241252741120"
TIP_HEIGHT = 1827840
QUERY_HEIGHT = 1820159
QUERY_ID = "83975c445cdb1626f78cd2ebddee25bc3418226931b27c9294b60bc923c0eaa9"
KEY_ID = "ee2f29a812da5ea75d28333792d1f5c83af876848e90113bb6fe68fc783affe6"
SOURCE_MANIFEST = "33d9a779c667297cb04387fee3ff12dcabbe2f34dff8eaff4522072a1c8c6048"
REFERENCE_EXE_SHA = {
    "N0": "3606870ad17e4fe6e1f3691591ebcfd54a76f85f4dafe8c3cdd47678a7b6c633",
    "N1": "5109cb8256f0b3f99ec2c68ee7ded38e0f1c37d6266c2753a80ccc6258c773a3",
}
PROFILES = {
    "N0": {
        "height": 1819648, "checkpoint": 1804171, "work": "2746167078539581456384",
        "tip": "b3fcd18faf8f028cb153999daa30743aaaf204ba15818564d8dc4da6e54fbe73",
        "checkpoint_id": "67e5e486c29a651ab7bc297e3f47188d78609aa355cd5db6ba19897e0f97bc78",
        "root": "c3b6c30cf5280dce4a67cf47959c3bcc67b7e00105d5391067c3ce930ab73a95",
    },
    "N1": {
        "height": TIP_HEIGHT, "checkpoint": 1810842, "work": TIP_WORK, "tip": TIP_ID,
        "checkpoint_id": "10dee2b41a0505ed3b5e59e77a080b9ac2b587a7e72ec45e644951cd5a9d1a77",
        "root": "93f74871644f3644e8cca9579c353006cb12ff50064f82e7660ab5ac552a307b",
    },
}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(path, algorithm):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, algorithm).hexdigest()


def is_link(path):
    meta = path.lstat()
    return stat.S_ISLNK(meta.st_mode) or bool(getattr(meta, "st_file_attributes", 0) & stat.FILE_ATTRIBUTE_REPARSE_POINT)


def check_sources(snapshot):
    require(snapshot in PROFILES, "Unknown snapshot")
    src = KIT / "source"
    manifest = KIT / "SOURCE-MANIFEST.tsv"
    require(manifest.is_file() and not is_link(manifest), "Source manifest missing or linked")
    raw = manifest.read_bytes()
    require(hashlib.sha256(raw).hexdigest() == SOURCE_MANIFEST, "Source manifest differs")
    require(src.is_dir() and not is_link(src), "Source directory missing or linked")
    expected = set()
    for line in raw.decode("utf-8-sig").splitlines():
        name, size, sha = line.split("\t")
        require(name and not any(x in ("", ".", "..") for x in name.split("/"))
                and ":" not in name and "\\" not in name and name not in expected, "Invalid source path")
        expected.add(name)
        path = src / name
        require(path.is_file() and not is_link(path) and path.stat().st_size == int(size)
                and digest(path, "sha256") == sha.lower(), f"Source mismatch: {name}")
    found = set()
    for parent, dirs, files in os.walk(src):
        for name in dirs:
            require(not is_link(Path(parent) / name), f"Linked source directory: {name}")
        found.update((Path(parent)/name).relative_to(src).as_posix() for name in files)
    require(found == expected, "Extra or missing source files")
    return src


def environment():
    env = {k: v for k,v in os.environ.items() if not k.upper().startswith(("NIPOPOW_", "RAYON_"))}
    env.update(RAYON_NUM_THREADS="4", RUST_TEST_THREADS="1", RUST_MIN_STACK="67108864", RUST_BACKTRACE="0")
    return env


def build(snapshot, src, work, offline, manifest=SOURCE_MANIFEST):
    cargo = shutil.which("cargo")
    require(cargo is not None, "Cargo is required to build the verifier")
    require(not work.is_relative_to(KIT), "Choose a build directory outside the kit")
    work.mkdir(parents=True, exist_ok=True)
    target = work / manifest.upper() / snapshot / "era-bound-review"
    env = environment()
    env.update(CARGO_TARGET_DIR=str(target), CARGO_INCREMENTAL="0", CARGO_BUILD_JOBS="2",
               CARGO_PROFILE_TEST_OPT_LEVEL="1", CARGO_PROFILE_TEST_DEBUG="0",
               CARGO_PROFILE_TEST_DEBUG_ASSERTIONS="true", CARGO_PROFILE_TEST_OVERFLOW_CHECKS="true")
    args = [cargo, "test", "--lib", "--no-run", "--locked", "--message-format=json"]
    if offline:
        args.append("--offline")
    if snapshot == "N0":
        args.extend(["--features", "h21-snapshot-n0"])
    artifacts = []
    finished = []
    with subprocess.Popen(args, cwd=src, env=env, stdout=subprocess.PIPE, text=True, encoding="utf-8") as proc:
        for line in proc.stdout:
            rec = json.loads(line)
            if rec.get("reason") == "compiler-message" and rec["message"]["level"] == "error":
                print(rec["message"].get("rendered", rec["message"]["message"]), file=sys.stderr)
            if rec.get("reason") == "build-finished":
                finished.append(rec["success"])
            if (rec.get("reason") == "compiler-artifact" and rec.get("executable")
                    and Path(rec["manifest_path"]).resolve() == (src/"Cargo.toml").resolve()
                    and rec["target"]["name"] == "nipopow_gkr_dory_prototype"
                    and rec["target"]["kind"] == ["lib"] and rec["profile"]["test"]
                    and rec["features"] == (["h21-snapshot-n0"] if snapshot == "N0" else [])):
                artifacts.append(Path(rec["executable"]).resolve())
        require(proc.wait() == 0 and finished == [True] and len(artifacts) == 1, "Verifier build did not finish")
    exe = artifacts[0]
    require(exe.is_file() and exe.is_relative_to(target), "Unexpected Cargo executable")
    return exe


def expect_fields(actual, expected, where):
    require(isinstance(actual, dict), f"Missing {where}")
    for name,value in expected.items():
        require(actual.get(name) == value, f"Unexpected {where}.{name}")

@contextmanager
def held_windows(path):
    """Open the regular file for reading and deny new writers or renames."""
    require(os.name == "nt", "This operation requires Windows")
    import ctypes
    from ctypes import wintypes
    import msvcrt
    path = path.absolute()
    for node in (*reversed(path.parents),path):
        require(not is_link(node), f"Linked input: {node}")
    require(path.is_file(), "Expected a regular file")
    api = ctypes.WinDLL("kernel32", use_last_error=True)
    create = api.CreateFileW
    create.argtypes = (wintypes.LPCWSTR, wintypes.DWORD, wintypes.DWORD, wintypes.LPVOID,
                       wintypes.DWORD, wintypes.DWORD, wintypes.HANDLE)
    create.restype = wintypes.HANDLE
    handle = create(str(path), 0x80000000, 1, None, 3, 0x00200000, None)
    if handle == wintypes.HANDLE(-1).value:
        raise ctypes.WinError(ctypes.get_last_error())
    try:
        fd = msvcrt.open_osfhandle(handle, os.O_RDONLY | os.O_BINARY)
    except OSError:
        api.CloseHandle(wintypes.HANDLE(handle))
        raise
    with os.fdopen(fd, "rb") as stream:
        require(stat.S_ISREG(os.fstat(stream.fileno()).st_mode), "Non-regular held file")
        yield stream


@contextmanager
def reference_executable(snapshot, path, pins=REFERENCE_EXE_SHA):
    with held_windows(path) as stream:
        require(hashlib.file_digest(stream, "sha256").hexdigest() == pins[snapshot],
                f"Different {snapshot} reference executable")
        yield path.resolve(strict=True)


def verify(snapshot, exe, certificate, extension, work):
    env = environment()
    env.update(NIPOPOW_V2_CERTIFICATES=str(certificate), NIPOPOW_V2_EXTENSIONS=str(extension),
               NIPOPOW_V2_EXACT_QUERY=str(QUERY_HEIGHT))
    proc = subprocess.run([str(exe), SELECTOR, "--exact", "--ignored", "--test-threads=1", "--nocapture"],
                          cwd=work, env=env, capture_output=True, text=True, encoding="utf-8")
    require(proc.returncode == 0, f"Native verifier failed ({proc.returncode}): {proc.stderr.strip() or proc.stdout[-1200:]}")
    require(re.search(r"(?m)^running 1 test$", proc.stdout) and f"test {SELECTOR} ..." in proc.stdout
            and re.search(r"(?m)^test result: ok\. 1 passed; 0 failed; 0 ignored;", proc.stdout),
            "The selected verifier did not run")
    reports = re.findall(r"(?m)\bV2_COLD_RECEIVER (\{[^\n]+\})$", proc.stdout)
    require(len(reports) == 1, "Expected one receiver report")
    report = json.loads(reports[0])
    if report.get("result") != "SELECTED":
        print(json.dumps(report, sort_keys=True), file=sys.stderr)
        raise ValueError(f"Verifier returned {report.get('result')}")
    profile = PROFILES[snapshot]
    expect_fields(report, dict(requested_exact_query=QUERY_HEIGHT, bootstrap_inputs=1, exact_tail_inputs=1,
                               frozen_input_payload_bytes=certificate.stat().st_size+extension.stat().st_size), "receiver")
    hash256 = lambda: hashlib.blake2b(digest_size=32)
    expect_fields(report.get("bootstrap"), dict(committed_tip_height=profile["height"], committed_tip_id=profile["tip"],
                  checkpoint_height=profile["checkpoint"], checkpoint_id=profile["checkpoint_id"], work_root=profile["root"],
                  committed_work=profile["work"], structural_key_id=KEY_ID, certificate_bytes=certificate.stat().st_size,
                  certificate_blake2b256=digest(certificate, hash256)), "bootstrap")
    exact = report.get("exact")
    expect_fields(exact, dict(query_height=QUERY_HEIGHT, query_id=QUERY_ID, tip_height=TIP_HEIGHT,
                  tip_id=TIP_ID, total_work=TIP_WORK, checked_tail_headers=TIP_HEIGHT-profile["checkpoint"],
                  extension_bytes=extension.stat().st_size, extension_blake2b256=digest(extension, hash256)), "exact")
    require(hashlib.blake2b(bytes.fromhex(exact["query_header_raw"]), digest_size=32).hexdigest() == QUERY_ID,
            "Returned query header differs")
    return report


def main():
    if len(sys.argv) > 1 and sys.argv[1] in ("prefix","check-prefix-sources","build-prefix"):
        sys.path.insert(0, str(KIT))
        import prefix_review
        return prefix_review.main(sys.argv[1:], KIT, check_sources, held_windows, reference_executable,
                                  build, environment)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["check-sources","build","verify"])
    parser.add_argument("snapshot", choices=PROFILES)
    parser.add_argument("packets", nargs="*", type=Path, metavar="FILE")
    parser.add_argument("--offline", action="store_true", help="use the local Cargo dependency cache")
    parser.add_argument("--work-dir", type=Path, default=Path(os.environ.get("LOCALAPPDATA") or Path.home()/".cache")/
                        "NiPoPoW"/"era-bound-review")
    parser.add_argument("--reference-binary", type=Path,
                        help="verify with the exact Windows reference image for this snapshot")
    args = parser.parse_intermixed_args()
    src = check_sources(args.snapshot)
    require(len(args.packets) == (2 if args.command == "verify" else 0), "verify takes one certificate and one extension")
    require(not args.reference_binary or args.command == "verify", "--reference-binary applies to verify")
    if args.command == "check-sources":
        print(f"{args.snapshot} source manifest verified: {SOURCE_MANIFEST}")
        return
    packets = [p.resolve(strict=True) for p in args.packets]
    for p in packets:
        require(p.is_file() and p.stat().st_size > 0 and not p.is_relative_to(src) and os.pathsep not in str(p),
                f"Expected one nonempty packet outside the Rust source tree: {p}")
    require(sum(p.stat().st_size for p in packets) <= 1 << 30, "Packet set exceeds the receiver staging budget")
    work = args.work_dir.resolve()
    require(not work.is_relative_to(KIT), "Choose a work directory outside the kit")
    if args.reference_binary:
        work.mkdir(parents=True, exist_ok=True)
        with reference_executable(args.snapshot, args.reference_binary) as exe:
            print(json.dumps(verify(args.snapshot, exe, *packets, work), indent=2))
        return
    exe = build(args.snapshot, src, work, args.offline)
    if args.command == "build":
        print(exe)
    else:
        print(json.dumps(verify(args.snapshot, exe, *packets, work), indent=2))


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"Verification error: {error}", file=sys.stderr)
        sys.exit(1)
