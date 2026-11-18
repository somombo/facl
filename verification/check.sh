#!/usr/bin/env bash
# Usage: verification/check.sh [--paranoid] [--no-extract]   (see README.md)
set -euo pipefail

verification_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
comparator_args=()
extract=true
for arg in "$@"; do
  case $arg in
    --paranoid) comparator_args+=(--paranoid) ;;
    --no-extract) extract=false ;;
    *) echo "usage: $0 [--paranoid] [--no-extract]" >&2; exit 2 ;;
  esac
done

fingerprint() {
  (cd "$verification_dir" && find FaclCore -type f -print0 2>/dev/null \
    | LC_ALL=C sort -z | xargs -0 -r sha256sum)
}

if $extract; then
  echo "==> Checking that FaclCore/ matches the Rust"
  before=$(fingerprint)
  "$verification_dir/extract.sh"
  if [[ $before != "$(fingerprint)" ]]; then
    echo "FaclCore/ was not what Aeneas generates from the Rust." >&2
    changed=$(git -C "$verification_dir" status --short -- FaclCore)
    if [[ -n $changed ]]; then
      echo "The regenerated files differ from the commit; commit them with the Rust change:" >&2
      echo "$changed" >&2
    else
      echo "The regenerated files match the commit, so FaclCore/ had local edits; they are replaced now." >&2
    fi
    exit 1
  fi
else
  echo "==> Skipping the extraction check: FaclCore/ is trusted as committed" >&2
fi

cd "$verification_dir"
echo "==> Building"
lake exe cache get
lake build --wfail
echo "==> Running lake comparator ${comparator_args[*]}"
lake comparator "${comparator_args[@]}"
