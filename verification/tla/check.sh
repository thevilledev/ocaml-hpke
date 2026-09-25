#!/bin/sh
# Model-check every configuration in this directory with TLC and compare the
# outcome with the expected one. Deadlock checking stays on for every run.
# The whole suite takes about a quarter of an hour, six minutes of it for
# HpkeContext_3dom.
#
#   JAVA=...  TLA2TOOLS=...  ./check.sh            # all runs
#   ./check.sh HpkeContext_3dom                    # selected runs
#
# TLC's metadata goes to a temporary directory, never into the repository.
set -u

JAVA=${JAVA:-/opt/homebrew/opt/openjdk/bin/java}
TLA2TOOLS=${TLA2TOOLS:-$HOME/.local/share/tlaplus/tla2tools.jar}
META=${TLC_METADIR:-$(mktemp -d "${TMPDIR:-/tmp}/hpke-tlc.XXXXXX")}
mkdir -p "$META" || exit 2

cd "$(dirname "$0")" || exit 2

# config  module  expected ("pass", or the violated property TLC names)
RUNS='
Rfc9180Context                         Rfc9180Context pass
HpkeContext                            HpkeContext    pass
HpkeContext_3dom                       HpkeContext    pass
HpkeContext_wide                       HpkeContext    pass
HpkeContext_async_cas                  HpkeContext    pass
HpkeContext_fixed                      HpkeContext    pass
HpkeContext_fixed_async                HpkeContext    pass
HpkeContext_fixed_async_wide           HpkeContext    pass
HpkeContext_fix_seq_async_incr         HpkeContext    pass
HpkeContext_fix_busy_async             HpkeContext    pass
HpkeChannel                            HpkeChannel    pass
HpkeContext_rfc_order                  HpkeContext    Refinement
HpkeContext_async_cas_stuck            HpkeContext    BusyReleased
HpkeContext_async_incr                 HpkeContext    NoNonceReuse
HpkeContext_async_incr_open            HpkeContext    NoNonceReuse
HpkeContext_async_incr_relaxed         HpkeContext    RelaxedRefinement
HpkeContext_async_release_stuck        HpkeContext    BusyReleased
HpkeContext_fixed_async_skips          HpkeContext    SeqCountsSuccesses
HpkeContext_mut_no_cas                 HpkeContext    NoNonceReuse
HpkeContext_mut_incr_before_aead       HpkeContext    Refinement
HpkeContext_mut_check_after_incr       HpkeContext    NeverUsesAllOnesNonce
HpkeContext_mut_release_before_incr    HpkeContext    NoNonceReuse
HpkeContext_mut_no_fun_protect         HpkeContext    BusyReleased
HpkeChannel_mut_advance_on_failure     HpkeChannel    NoDesync
HpkeChannel_mut_advance_on_failure_liveness HpkeChannel EventuallyAccepted
HpkeChannel_mut_ignore_aad             HpkeChannel    AcceptedIsPrefixOfSealed
'

for spec in Rfc9180Context HpkeContext HpkeChannel; do
  "$JAVA" -cp "$TLA2TOOLS" tla2sany.SANY "$spec.tla" > "$META/sany-$spec.log" 2>&1
  if grep -q -i "error" "$META/sany-$spec.log"; then
    echo "SANY failed on $spec.tla, see $META/sany-$spec.log"; exit 1
  fi
done

status=0
while read -r cfg module expected; do
  [ -z "$cfg" ] && continue
  if [ $# -gt 0 ]; then
    case " $* " in *" $cfg "*) ;; *) continue ;; esac
  fi
  log="$META/$cfg.log"
  "$JAVA" -XX:+UseParallelGC -cp "$TLA2TOOLS" tlc2.TLC -workers auto \
    -metadir "$META/$cfg" -config "$cfg.cfg" "$module.tla" < /dev/null > "$log" 2>&1
  states=$(grep -E 'distinct states found' "$log" | tail -1 |
           sed -E 's/.* ([0-9 ]+) distinct states found.*/\1/' | tr -d ' ')
  took=$(grep -E '^Finished in' "$log" | sed -E 's/^Finished in (.*) at .*/\1/')
  if grep -q 'No error has been found' "$log"; then
    got=pass
  elif grep -q 'Temporal properties were violated' "$log"; then
    got=temporal
  else
    got=$(grep -m1 -E 'Invariant .* is violated|Action property .* is violated' "$log" |
          sed -E 's/.*Invariant ([A-Za-z]+) is violated.*/\1/;
                  s/.*Action property .* of module Rfc9180Context is violated.*/Refinement/')
    # An action property defined in the checked module: name the definition
    # that contains the line TLC reports.
    case "$got" in
      *"Action property line "*)
        line=$(echo "$got" | sed -E 's/.*Action property line ([0-9]+),.*/\1/')
        got=$(awk -v l="$line" 'NR <= l && /^[A-Za-z][A-Za-z0-9_]* *==/ { n = $1 }
                                NR == l { print n; exit }' "$module.tla") ;;
    esac
  fi
  # TLC does not name a violated temporal property; the configs that
  # expect one check exactly one.
  case "$expected:$got" in
    pass:pass) verdict=ok ;;
    BusyReleased:temporal|EventuallyAccepted:temporal) verdict=ok ;;
    *:"$expected") verdict=ok ;;
    *) verdict=UNEXPECTED; status=1 ;;
  esac
  printf '%-44s %-24s %-10s %10s states  %s\n' "$cfg" "expected=$expected" "$verdict" "${states:-?}" "${took:-?}"
done <<EOF
$RUNS
EOF
echo "TLC logs: $META"
exit $status
