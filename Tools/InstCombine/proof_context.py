"""Fingerprint local Lean inputs so changing dependencies invalidates proof records."""
import hashlib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def proof_context_sha256():
    paths = set((ROOT / 'Veir').rglob('*.lean'))
    paths.update((ROOT / 'UnitTest').rglob('*.lean'))
    for name in ('lean-toolchain', 'lakefile.lean', 'lakefile.toml', 'lake-manifest.json'):
        path = ROOT / name
        if path.is_file():
            paths.add(path)
    digest = hashlib.sha256()
    for path in sorted(paths):
        digest.update(str(path.relative_to(ROOT)).encode() + b'\0')
        digest.update(hashlib.sha256(path.read_bytes()).digest())
    return digest.hexdigest()
