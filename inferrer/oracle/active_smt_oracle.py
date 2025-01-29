from inferrer.oracle import ActiveOracle
from inferrer import automaton
from typing import Tuple
from inferrer.smt_utils import z3_strings
class ActiveSMTOracle(ActiveOracle):
    def __init__(self, fsa: automaton.FSA):
        super().__init__(fsa)
        self._fsa_regex = fsa.to_regex() or "EMPTYREGEX"


    def equivalence_query(self, fsa: automaton.FSA) -> Tuple[str, bool]:
        query_regex = fsa.to_regex() or "EMPTYREGEX"
        isEqual, word = z3_strings.check_raw_regex_equivalence(self._fsa_regex, query_regex)
        if isEqual:
            return '', True
        else:
            return word, False