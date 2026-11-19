#!/usr/bin/env bash
set -euo pipefail

verification_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
work_dir=$(mktemp -d)
trap 'rm -rf -- "$work_dir"' EXIT

# Keep this revision in sync with the Lean dependency in lakefile.toml.
aeneas_flake=github:AeneasVerif/aeneas/1dc8ad31b1b062a77c50e29144a6c7bba955fa09
if [[ -n ${CHARON:-} || -n ${AENEAS:-} ]]; then
  charon=("${CHARON:?set CHARON and AENEAS together}")
  aeneas=("${AENEAS:?set CHARON and AENEAS together}")
else
  charon=(nix run "$aeneas_flake#charon" -L --)
  aeneas=(nix run "$aeneas_flake" -L --)
fi

llbc="$work_dir/facl_core.llbc"
(
  cd "$verification_dir/../crates/facl-core"
  CARGO_TARGET_DIR="$work_dir/target" "${charon[@]}" cargo --preset=aeneas --sysroot=default \
    --start-from=crate::decide::evaluate_with --start-from=crate::decide::combine --start-from=crate::decide::method_bit \
    --start-from=crate::path::canonicalize \
    --start-from=crate::path::match_pattern --start-from=crate::decide::decide_with \
    --start-from=crate::lower::lower_with --start-from=crate::decide::action_bits --dest-file="$llbc" -- --locked
)

"${aeneas[@]}" -backend lean -loops-to-rec -split-files -namespace FaclCore \
  -abort-on-error -no-progress-bar -dest "$work_dir" -subdir /FaclCore "$llbc"

generated="$work_dir/FaclCore"
if [[ ! -f "$generated/Types.lean" || ! -f "$generated/Funs.lean" ]]; then
  echo "Aeneas did not produce Types.lean and Funs.lean" >&2
  exit 1
fi
template=$(find "$generated" -name '*_Template.lean' -print -quit)
if [[ -n $template ]]; then
  echo "Aeneas template requires a Lean model: ${template#"$generated"/}" >&2
  exit 1
fi

destination="$verification_dir/FaclCore"
if [[ -L $destination ]]; then
  echo "Output directory $destination is a symbolic link" >&2
  exit 1
fi
rsync --archive --checksum --delay-updates --delete-after -- "$generated/" "$destination/"
