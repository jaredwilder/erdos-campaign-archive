#!/bin/bash
cd /root/mathlib4
export PATH=/root/.elan/bin:$PATH
run_one() {
  b=$(basename "$1" .lean)
  timeout 300 lake env lean "$1" > /root/peer/out/s20260902_092141_1/$b.log 2>&1
  echo $? > /root/peer/out/s20260902_092141_1/$b.rc
}
export -f run_one
ls /root/peer/strengthen/s20260902_092141_1/*.lean | xargs -P 8 -I{} bash -c 'run_one "$@"' _ {}
touch /root/peer/out/s20260902_092141_1/DONE

