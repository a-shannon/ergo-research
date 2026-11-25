//! Portable locations for opt-in external-fixture tests.
use std::path::{Component, Path, PathBuf};

fn resolved(path: &Path) -> Option<PathBuf> {
    let existing = path.ancestors().find(|ancestor| ancestor.exists())?;
    let suffix = path.strip_prefix(existing).ok()?;
    if suffix.components().any(|part| !matches!(part, Component::Normal(_) | Component::CurDir)) {
        return None;
    }
    Some(existing.canonicalize().ok()?.join(suffix))
}

pub(crate) fn absolute_outside_source(path: &Path) -> bool {
    if !path.is_absolute() {
        return false;
    }
    let Some(path) = resolved(path) else { return false };
    let Ok(source) = Path::new(env!("CARGO_MANIFEST_DIR")).canonicalize() else { return false };
    path.parent().is_some() && !path.starts_with(source)
}
