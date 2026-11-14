#!/bin/sh
# setup-iris.sh [DIR]: builds std++ and Iris at the commits FrFlow's proofs about threads were checked with, and
# installs them where `rocq` looks (its user-contrib). Needs Rocq 9.0 to 9.3, git and make; about half an hour.
#   bin/setup-iris.sh /tmp/iris-src
set -e
dir="${1:-${TMPDIR:-/tmp}/frflow-iris}"
jobs="${JOBS:-3}"
mkdir -p "$dir"
fetch() {  # name commit
  [ -d "$dir/$1/.git" ] || git clone -q "https://gitlab.mpi-sws.org/iris/$1.git" "$dir/$1"
  git -C "$dir/$1" fetch -q origin && git -C "$dir/$1" checkout -q "$2"
}
fetch stdpp e306670eb3680b02503d7fbdaf35ae5a55b02944
fetch iris f58daaf453c424efe57c511a607229debc71dbfe
(cd "$dir/stdpp" && ./make-package stdpp "-j$jobs" && ./make-package stdpp install)
(cd "$dir/iris" && ./make-package iris "-j$jobs" && ./make-package iris install)
echo "std++ and Iris installed under $(rocq -where)/user-contrib"
