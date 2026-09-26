#!/usr/bin/env python3
"""Extract the supported draft-ietf-hpke-pq vectors into a compact test corpus."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


# The commit tagged draft-ietf-hpke-pq-05.
SOURCE_COMMIT = "6433c8fce0b8b749dfc86c1095081a88698ccfab"
SOURCE_SHA256 = "35c59f4a0132e5631e50ac039d8ca3a72e99f5e92dfd94d45338d6ae243f613c"
SOURCE_URL = (
    "https://raw.githubusercontent.com/hpkewg/hpke-pq/"
    f"{SOURCE_COMMIT}/test-vectors.json"
)
SUPPORTED_MODES = {0, 1}
MLKEM_KEMS = {0x0040, 0x0041, 0x0042}
# MLKEM768-P256, MLKEM1024-P384, and MLKEM768-X25519.
HYBRID_KEMS = {0x0050, 0x0051, 0x647A}
SUPPORTED_KEMS = MLKEM_KEMS | HYBRID_KEMS
SUPPORTED_KDFS = {0x0001, 0x0002, 0x0003}
# SHAKE128 and SHAKE256, the one-stage KDFs that Hpke.Draft_hpke_04 provides.
DRAFT_KDFS = {0x0010, 0x0011, 0x0012, 0x0013}
DH_KEMS = {0x0010, 0x0011, 0x0012, 0x0020, 0x0021}
SUPPORTED_AEADS = {0x0001, 0x0002, 0x0003, 0xFFFF}
COPIED_FIELDS = (
    "mode",
    "kem_id",
    "kdf_id",
    "aead_id",
    "info",
    # The randomness of the deterministic encapsulation, EncapDerand.
    "ikmE",
    "ikmR",
    "skRm",
    "pkRm",
    "enc",
    "psk",
    "psk_id",
    # Key-schedule outputs: the published key is a known answer for the
    # single-shot AEAD entry points. Unlike the RFC 9180 corpus, this one
    # publishes no key_schedule_context or secret.
    "shared_secret",
    "key",
    "base_nonce",
    "exporter_secret",
    "encryptions",
    "exports",
)
# An ML-KEM or hybrid key pair and encapsulation do not depend on the rest of
# the suite. A vector whose KDF is not supported is therefore still a known
# answer for DeriveKeyPair and for the encapsulation, and keeps the fields of
# those alone.
KEM_ONLY_FIELDS = ("kem_id", "kdf_id", "ikmE", "ikmR", "skRm", "pkRm", "enc")


def supported_kem(vector: dict[str, Any]) -> bool:
    return vector["mode"] in SUPPORTED_MODES and vector["kem_id"] in SUPPORTED_KEMS


def draft_selected(vector: dict[str, Any]) -> bool:
    return (
        vector["mode"] in SUPPORTED_MODES
        and vector["kem_id"] in SUPPORTED_KEMS | DH_KEMS
        and vector["kdf_id"] in DRAFT_KDFS
        and vector["aead_id"] in SUPPORTED_AEADS
    )


def selected(vector: dict[str, Any]) -> bool:
    return (
        supported_kem(vector)
        and vector["kdf_id"] in SUPPORTED_KDFS
        and vector["aead_id"] in SUPPORTED_AEADS
    )


def reduce_vector(vector: dict[str, Any], fields: tuple[str, ...]) -> dict[str, Any]:
    return {field: vector[field] for field in fields if field in vector}


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
    vectors = [
        reduce_vector(vector, COPIED_FIELDS) for vector in source if selected(vector)
    ]
    if len(vectors) != 6:
        raise SystemExit(f"expected 6 supported vectors, found {len(vectors)}")
    if {vector["kem_id"] for vector in vectors} != SUPPORTED_KEMS:
        raise SystemExit("expected a supported vector for every supported KEM")

    draft_vectors = [
        reduce_vector(vector, COPIED_FIELDS) for vector in source if draft_selected(vector)
    ]
    if len(draft_vectors) != 7:
        raise SystemExit(f"expected 7 SHA-3 vectors, found {len(draft_vectors)}")
    if {vector["kdf_id"] for vector in draft_vectors} != DRAFT_KDFS:
        raise SystemExit("expected SHAKE vectors for both SHAKE KDFs")

    kem_only_vectors: list[dict[str, Any]] = [
        reduce_vector(vector, KEM_ONLY_FIELDS)
        for vector in source
        if supported_kem(vector) and not selected(vector) and not draft_selected(vector)
    ]
    if kem_only_vectors:
        raise SystemExit(f"expected no KEM-only vector, found {len(kem_only_vectors)}")

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
            "draft_kdfs": sorted(DRAFT_KDFS),
            "aeads": sorted(SUPPORTED_AEADS),
        },
        "vectors": vectors,
        # For Hpke.Draft_hpke_04 alone: suites with a one-stage KDF.
        "draft_vectors": draft_vectors,
        "kem_only_vectors": kem_only_vectors,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(output, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )


if __name__ == "__main__":
    main()
