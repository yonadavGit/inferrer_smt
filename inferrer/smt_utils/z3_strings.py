from z3 import *
import z3
import sre_parse, sre_constants


def regex_to_z3_re(pattern: str) -> ReRef:
    """
    Convert a regular expression pattern to a Z3 regular expression.
    Supports basic operations: concatenation (.), alternation (|),
    character ranges ([a-z]), Kleene star (*), and parentheses for grouping ().

    Args:
        pattern: String containing the regular expression pattern

    Returns:
        Z3 regular expression

    Raises:
        ValueError: If the pattern contains syntax errors or mismatched parentheses
    """

    def parse_char_range(range_str):
        # Handle character range like [a-z]
        start, end = range_str[1:-1].split('-')
        return Union([Re(StringVal(chr(i))) for i in range(ord(start), ord(end) + 1)])

    def find_matching_parenthesis(pattern, start_pos):
        """Find the position of the matching closing parenthesis."""
        count = 1
        pos = start_pos
        while pos < len(pattern) and count > 0:
            if pattern[pos] == '(':
                count += 1
            elif pattern[pos] == ')':
                count -= 1
            pos += 1

        if count > 0:
            raise ValueError("Mismatched parentheses")
        return pos - 1

    def parse_regex(pattern, pos=0, end=None):
        if end is None:
            end = len(pattern)

        terms = []
        current_term = []

        while pos < end:
            char = pattern[pos]

            if char == '(':
                # Handle nested expression
                closing_pos = find_matching_parenthesis(pattern, pos + 1)
                nested_term = parse_regex(pattern, pos + 1, closing_pos)
                current_term.append(nested_term)
                pos = closing_pos + 1
            elif char == ')':
                raise ValueError("Unexpected closing parenthesis")
            elif char == '|':
                # Handle alternation
                if current_term:
                    terms.append(make_concat(current_term))
                    current_term = []
                pos += 1
            elif char == '[':
                # Find the closing bracket
                end_pos = pattern.find(']', pos)
                if end_pos == -1:
                    raise ValueError("Unclosed character range")
                range_term = parse_char_range(pattern[pos:end_pos + 1])
                current_term.append(range_term)
                pos = end_pos + 1
            elif char == '*':
                # Handle Kleene star
                if not current_term:
                    raise ValueError("Invalid Kleene star position")
                last_term = current_term.pop()
                current_term.append(Star(last_term))
                pos += 1
            else:
                # Handle literal character
                current_term.append(Re(StringVal(char)))
                pos += 1

        if current_term:
            terms.append(make_concat(current_term))

        # Combine all terms with union
        if not terms:
            raise ValueError("Empty regular expression")
        elif len(terms) == 1:
            return terms[0]
        else:
            return Union(terms)

    def make_concat(terms):
        if len(terms) == 1:
            return terms[0]
        return Concat(terms)

    return parse_regex(pattern)

def check_raw_regex_equivalence(reg1: str, reg2: str):
    reg1_ast = sre_parse.parse(reg1)
    reg2_ast = sre_parse.parse(reg2)
    reg1_symbolic = regex_to_z3_expr(reg1_ast)
    reg2_symbolic = regex_to_z3_expr(reg2_ast)

    # reg1_symbolic = regex_to_z3_re(reg1)
    # reg2_symbolic = regex_to_z3_re(reg2)
    result = check_regex_equivalence(reg1_symbolic, reg2_symbolic)
    return result


# def check_regex_equivalence(solver, reg1: ReRef, reg2: ReRef):
#     """
#     Check if two regular expressions are equivalent.
#     Returns (True, None) if they are equivalent,
#     otherwise returns (False, s) where s is a distinguishing string.
#
#     Args:
#         solver: Z3 solver instance
#         reg1: First regular expression as Z3 ReRef
#         reg2: Second regular expression as Z3 ReRef
#
#     Returns:
#         tuple[bool, str | None]: (is_equivalent, distinguishing_string)
#     """
#     # Create a string variable
#     s = String('s')
#
#     # Check for a string that belongs to one regex but not the other
#     solver.push()
#     solver.add(
#         Or(
#             And(InRe(s, reg1), Not(InRe(s, reg2))),
#             And(InRe(s, reg2), Not(InRe(s, reg1)))
#         )
#     )
#
#     if solver.check() == sat:
#         # Get the distinguishing string
#         model = solver.model()
#         distinguishing_string = model[s].as_string()
#         solver.pop()
#         return False, distinguishing_string
#     else:
#         solver.pop()
#         return True, None
def check_regex_equivalence(reg1, reg2):
    s = String('s')
    solver = Solver()

    # Create regex for symmetric difference (R1\R2 ∪ R2\R1)
    # This captures strings that are in one regex but not the other
    symmetric_diff = Union(
        Diff(reg1, reg2),  # Strings in reg1 but not in reg2
        Diff(reg2, reg1)  # Strings in reg2 but not in reg1
    )

    # Check if there exists a string in the symmetric difference
    solver.add(InRe(s, symmetric_diff))

    if solver.check() == sat:
        # Found a witness showing the regexes are not equivalent
        model = solver.model()
        return False, model[s].as_string()
    else:
        # No witness found, regexes are equivalent
        return True, None
# Translates a specific regex construct into its Z3 equivalent.
def regex_construct_to_z3_expr(regex_construct) -> z3.ReRef:
  node_type, node_value = regex_construct
  if sre_constants.LITERAL == node_type: # a
    return z3.Re(chr(node_value))
  if sre_constants.NOT_LITERAL == node_type: # [^a]
    return Minus(AnyChar(), z3.Re(chr(node_value)))
  if sre_constants.SUBPATTERN == node_type:
    _, _, _, value = node_value
    return regex_to_z3_expr(value)
  elif sre_constants.ANY == node_type: # .
    return AnyChar()
  elif sre_constants.MAX_REPEAT == node_type:
    low, high, value = node_value
    if (0, 1) == (low, high): # a?
      return z3.Option(regex_to_z3_expr(value))
    elif (0, sre_constants.MAXREPEAT) == (low, high): # a*
      return z3.Star(regex_to_z3_expr(value))
    elif (1, sre_constants.MAXREPEAT) == (low, high): # a+
      return z3.Plus(regex_to_z3_expr(value))
    else: # a{3,5}, a{3}
      return z3.Loop(regex_to_z3_expr(value), low, high)
  elif sre_constants.IN == node_type: # [abc]
    first_subnode_type, _ = node_value[0]
    if sre_constants.NEGATE == first_subnode_type: # [^abc]
      return Minus(AnyChar(), z3.Union([regex_construct_to_z3_expr(value) for value in node_value[1:]]))
    else:
      return z3.Union([regex_construct_to_z3_expr(value) for value in node_value])
  elif sre_constants.BRANCH == node_type: # ab|cd
    _, value = node_value
    return z3.Union([regex_to_z3_expr(v) for v in value])
  elif sre_constants.RANGE == node_type: # [a-z]
    low, high = node_value
    return z3.Range(chr(low), chr(high))
  elif sre_constants.CATEGORY == node_type: # \d, \s, \w
    if sre_constants.CATEGORY_DIGIT == node_value: # \d
      return category_regex(node_value)
    elif sre_constants.CATEGORY_NOT_DIGIT == node_value: # \D
      return Minus(AnyChar(), category_regex(sre_constants.CATEGORY_DIGIT))
    elif sre_constants.CATEGORY_SPACE == node_value: # \s
      return category_regex(node_value)
    elif sre_constants.CATEGORY_NOT_SPACE == node_value: # \S
      return Minus(AnyChar(), category_regex(sre_constants.CATEGORY_SPACE))
    elif sre_constants.CATEGORY_WORD == node_value: # \w
      return category_regex(node_value)
    elif sre_constants.CATEGORY_NOT_WORD == node_value: # \W
      return Minus(AnyChar(), category_regex(sre_constants.CATEGORY_WORD))
    else:
      raise NotImplementedError(f'ERROR: regex category {node_value} not implemented')
  elif sre_constants.AT == node_type:
    if node_value in {sre_constants.AT_BEGINNING, sre_constants.AT_BEGINNING_STRING}: # ^a, \A
      raise NotImplementedError(f'ERROR: regex position {node_value} not implemented')
    elif sre_constants.AT_BOUNDARY == node_value: # \b
      raise NotImplementedError(f'ERROR: regex position {node_value} not implemented')
    elif sre_constants.AT_NON_BOUNDARY == node_value: # \B
      raise NotImplementedError(f'ERROR: regex position {node_value} not implemented')
    elif node_value in {sre_constants.AT_END, sre_constants.AT_END_STRING}: # a$, \Z
      raise NotImplementedError(f'ERROR: regex position {node_value} not implemented')
    else:
      raise NotImplementedError(f'ERROR: regex position {node_value} not implemented')
  else:
    raise NotImplementedError(f'ERROR: regex construct {regex_construct} not implemented')

# Translates a parsed regex into its Z3 equivalent.
# The parsed regex is a sequence of regex constructs (literals, *, +, etc.)
def regex_to_z3_expr(regex : sre_parse.SubPattern) -> z3.ReRef:
  if 0 == len(regex.data):
    # raise ValueError('ERROR: regex is empty')
    return z3.Re("")
  elif 1 == len(regex.data):
    return regex_construct_to_z3_expr(regex[0])
  else:
    return z3.Concat([regex_construct_to_z3_expr(construct) for construct in regex.data])

def get_solver():
    return Solver()

# Example usage:
if __name__ == "__main__":
    solver = Solver()
    # regex_term1 = regex_to_z3_re(solver, "(ab)*")
    # regex_term2 = regex_to_z3_re(solver, "ab*(ab)*")
    regex_term1 = regex_to_z3_expr(sre_parse.parse("(ab)*"))
    regex_term2 = regex_to_z3_expr(sre_parse.parse("(ab)*(ab)*"))
    result = check_regex_equivalence(solver, regex_term1, regex_term2)
    print(result)