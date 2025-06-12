#!/usr/bin/env bash
set -euo pipefail

##
# Ensure fd command is available. On Ubuntu the binary is fdfind.
# Creates a symlink to /usr/local/bin/fd if needed.
##
fd_normalize() {
	if ! command -v fd >/dev/null 2>&1; then
		sudo ln -sf "$(command -v fdfind)" /usr/local/bin/fd
	fi
}

##
# Populate the repeated_basenames array with file names that appear
# more than once in the repository.
##
gather_repeated_basenames() {
	mapfile -d "" -t repeated_basenames < <(
		fd --type f -0 | xargs -0 -n1 basename -a |
			sort -z | uniq -dz
	)
}

##
# For a given basename, collect all matching file paths into the
# paths array.
# Arguments:
#   $1 - basename to search for
##
collect_paths() {
	local base="$1"
	mapfile -d "" -t paths < <(
		fd --type f -0 -c never -a -t f --exact-depth 0 -x echo -n {} -0 |
			grep -z "/${base}$"
	)
}

##
# Process one basename: check for identical duplicates with fdupes
# and invoke meld for differing files.
# Arguments:
#   $1 - basename to process
##
process_basename() {
	local base="$1"
	printf '\n\e[1;36m» Group: %s\e[0m\n' "$base"
	collect_paths "$base"

	if fdupes -r1 -q "${paths[@]}" >/dev/null; then
		echo "  ✔ All duplicates are binary-identical – you may safely delete extras:"
		printf '    %s\n' "${paths[@]:1}"
		return
	fi

	echo "  ⚡ Divergent copies detected – launching meld for synthesis…"
	if ((${#paths[@]} <= 3)); then
		meld "${paths[@]}"
	else
		for ((i = 0; i < ${#paths[@]}; i += 3)); do
			meld "${paths[@]:i:3}" &
		done
	fi
}

main() {
	fd_normalize
	gather_repeated_basenames
	for base in "${repeated_basenames[@]}"; do
		process_basename "$base"
	done
}

main "$@"
