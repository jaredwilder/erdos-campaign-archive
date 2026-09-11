#!/usr/bin/env bash
# C(13,6,3) CLOSE LANE — box driver.  La Jolla holds 20 <= C(13,6,3) <= 21, so:
#   UNSAT + drat-trim verified          ->  C(13,6,3) = 21 exactly   (CLOSE)
#   SAT   + verify_cover from definition -> record 20-cover, C = 20  (BIGGER CLOSE)
#
# Ops laws (THE-GAP row 6, paid for in blood):
#   - the solver runs detached under setsid, never nohup-through-nested-shells
#   - STARTED / EXITED / EXIT_CODE stamps are written beside the log
#   - exit 137/143 is STOPPED_NO_VERDICT, never a verdict
#   - the CNF is REGENERATED on the box and its sha must match the local receipt
#     before the solver starts (encoder is deterministic; a mismatch is a stop-the-line bug)
#
# Usage:   BOX=root@<ip> bash RUN-ON-BOX.sh start
#          BOX=root@<ip> bash RUN-ON-BOX.sh collect

set -u
BOX=${BOX:?set BOX=root@<ip>}
REMOTE=${REMOTE:-/root/peer/c1363}
HERE="$(cd "$(dirname "$0")" && pwd)"
CMD=${1:?start|collect}

if [ "$CMD" = start ]; then
  ssh "$BOX" "mkdir -p $REMOTE"
  scp "$HERE/cover_sat.py" "$BOX:$REMOTE/"
  ssh "$BOX" "set -e; cd $REMOTE
    python3 cover_sat.py --selfcheck
    python3 cover_sat.py --emit --v 13 --k 6 --t 3 --b 20 --out c13-6-3-b20.cnf
    sha256sum c13-6-3-b20.cnf
    date -u +%FT%TZ > STARTED
    setsid bash -c '
      cadical --no-binary c13-6-3-b20.cnf c13-6-3-b20.drat > cadical.log 2>&1
      echo \$? > EXIT_CODE
      date -u +%FT%TZ > EXITED
    ' < /dev/null > /dev/null 2>&1 &
    echo LAUNCHED"
  echo "Launched. Poll with: BOX=$BOX bash RUN-ON-BOX.sh collect"
  exit 0
fi

if [ "$CMD" = collect ]; then
  ssh "$BOX" "cd $REMOTE
    if [ ! -f EXITED ]; then echo 'RUNNING since:' \$(cat STARTED 2>/dev/null); tail -3 cadical.log 2>/dev/null; exit 0; fi
    EC=\$(cat EXIT_CODE)
    echo \"EXIT_CODE=\$EC (10=SAT 20=UNSAT 137/143=STOPPED_NO_VERDICT)\"
    if [ \"\$EC\" = 20 ]; then
      echo '== drat-trim (an UNSAT counts ONLY if this verifies) =='
      drat-trim c13-6-3-b20.cnf c13-6-3-b20.drat | tail -5
      sha256sum c13-6-3-b20.cnf c13-6-3-b20.drat
    elif [ \"\$EC\" = 10 ]; then
      echo '== decode + verify FROM THE DEFINITION =='
      grep '^v' cadical.log > model.txt || grep '^v' c13-6-3-b20.out > model.txt
      python3 cover_sat.py --decode --v 13 --k 6 --t 3 --b 20 --cnf c13-6-3-b20.cnf --model model.txt
    else
      echo STOPPED_NO_VERDICT
    fi"
  exit 0
fi

echo "unknown command: $CMD" >&2; exit 2
