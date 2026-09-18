#!/usr/bin/env python3
"""Extract the supported RFC 9180 vectors into a compact test corpus."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


SOURCE_COMMIT = "5f503c564da00b0687b3de75f1dfbdfc4079ad31"
SOURCE_SHA256 = "61fc662f01996cd06d713dacf5e133167bd309a1f329442d53f1e21a47b3ede6"
SOURCE_URL = (
    "https://raw.githubusercontent.com/cfrg/draft-irtf-cfrg-hpke/"
    f"{SOURCE_COMMIT}/test-vectors.json"
)
SUPPORTED_MODES = {0, 1}
SUPPORTED_KEMS = {0x0010, 0x0012, 0x0020}
SUPPORTED_KDFS = {0x0001, 0x0003}
SUPPORTED_AEADS = {0x0001, 0x0002, 0x0003, 0xFFFF}
FULL_SEQUENCE_SUITES = {
    (0, 0x0020, 0x0001, 0x0001),
    (0, 0x0012, 0x0003, 0x0002),
    (0, 0x0020, 0x0001, 0x0003),
}
COPIED_FIELDS = (
    "mode",
    "kem_id",
    "kdf_id",
    "aead_id",
    "info",
    "ikmE",
    "skEm",
    "pkEm",
    "ikmR",
    "skRm",
    "pkRm",
    "enc",
    "psk",
    "psk_id",
    # Key-schedule intermediates: known answers for the unlabeled KDF and
    # single-shot AEAD entry points.
    "shared_secret",
    "key_schedule_context",
    "secret",
    "key",
    "base_nonce",
    "exporter_secret",
    "exports",
)


def selected(vector: dict[str, Any]) -> bool:
    return (
        vector["mode"] in SUPPORTED_MODES
        and vector["kem_id"] in SUPPORTED_KEMS
        and vector["kdf_id"] in SUPPORTED_KDFS
        and vector["aead_id"] in SUPPORTED_AEADS
    )


def reduce_vector(vector: dict[str, Any]) -> dict[str, Any]:
    result = {field: vector[field] for field in COPIED_FIELDS if field in vector}
    suite = tuple(vector[field] for field in ("mode", "kem_id", "kdf_id", "aead_id"))
    encryptions = vector["encryptions"]
    result["encryptions"] = (
        encryptions if suite in FULL_SEQUENCE_SUITES else encryptions[:3]
    )
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path, help="pinned upstream test-vectors.json")
    parser.add_argument("output", type=Path, help="path for the reduced corpus")
    args = parser.parse_args()

    source_bytes = args.input.read_bytes()
    source_sha256 = hashlib.sha256(source_bytes).hexdigest()
    if source_sha256 != SOURCE_SHA256:
        raise SystemExit(
            f"expected source SHA-256 {SOURCE_SHA256}, found {source_sha256}"
        )
    source = json.loads(source_bytes)
    vectors = [reduce_vector(vector) for vector in source if selected(vector)]
    if len(vectors) != 48:
        raise SystemExit(f"expected 48 supported vectors, found {len(vectors)}")

    full_sequences = [
        vector for vector in vectors if len(vector["encryptions"]) == 257
    ]
    if len(full_sequences) != 3:
        raise SystemExit(
            f"expected 3 complete encryption sequences, found {len(full_sequences)}"
        )

    output = {
        "source": {
            "url": SOURCE_URL,
            "commit": SOURCE_COMMIT,
            "sha256": source_sha256,
        },
        "selection": {
            "modes": sorted(SUPPORTED_MODES),
            "kems": sorted(SUPPORTED_KEMS),
            "kdfs": sorted(SUPPORTED_KDFS),
            "aeads": sorted(SUPPORTED_AEADS),
            "default_encryption_count": 3,
            "full_sequence_suites": [list(suite) for suite in sorted(FULL_SEQUENCE_SUITES)],
        },
        "vectors": vectors,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(output, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )


if __name__ == "__main__":
    main()
