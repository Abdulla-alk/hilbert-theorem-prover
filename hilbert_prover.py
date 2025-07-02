import re
from collections import deque, defaultdict
import itertools

class Formula:
    def __init__(self, kind, *args):
        self.kind = kind
        if kind == 'var':
            self.name = args[0]
        elif kind == 'not':
            self.child = args[0]
        else:
            self.left, self.right = args

    def __eq__(self, other):
        if not isinstance(other, Formula) or self.kind != other.kind:
            return False
        if self.kind == 'var':
            return self.name == other.name
        if self.kind == 'not':
            return self.child == other.child
        return self.left == other.left and self.right == other.right

    def __hash__(self):
        if self.kind == 'var':
            return hash((self.kind, self.name))
        if self.kind == 'not':
            return hash((self.kind, self.child))
        return hash((self.kind, self.left, self.right))

    def __str__(self):
        if self.kind == 'var':
            return self.name
        if self.kind == 'not':
            c = str(self.child)
            return f"~{c}" if self.child.kind == 'var' else f"~({c})"
        op = {'imp': '->'}[self.kind]
        l, r = str(self.left), str(self.right)
        return f"({l}{op}{r})"

    def variables(self):
        if self.kind == 'var':
            return {self.name}
        if self.kind == 'not':
            return self.child.variables()
        return self.left.variables() | self.right.variables()

def tokenize(s: str):
    s = s.replace(' ', '')
    token_pattern = r'->|[~()]|[A-Za-z][A-Za-z0-9_]*'
    return re.findall(token_pattern, s)

def parse_formula(s: str) -> Formula:
    tokens = tokenize(s)
    pos = 0

    def peek():
        return tokens[pos] if pos < len(tokens) else None

    def consume(expected=None):
        nonlocal pos
        tok = tokens[pos]
        if expected and tok != expected:
            raise ValueError(f"Expected {expected}, got {tok}")
        pos += 1
        return tok

    def parse_imp():
        left = parse_not()
        if peek() == '->':
            consume('->')
            right = parse_imp()
            return Formula('imp', left, right)
        return left

    def parse_not():
        if peek() == '~':
            consume('~')
            return Formula('not', parse_not())
        return parse_atom()

    def parse_atom():
        if peek() == '(': 
            consume('(')
            f = parse_imp()
            consume(')')
            return f
        tok = peek()
        if re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', tok):
            consume()
            return Formula('var', tok)
        raise ValueError(f"Unexpected token: {tok}")

    result = parse_imp()
    if pos != len(tokens):
        raise ValueError("Extra tokens after parsing.")
    return result

# --- Hilbert Axiom Schemas ---
# A1: A -> (B -> A)
# A2: (A -> (B -> C)) -> ((A -> B) -> (A -> C))
# A3: (~A -> ~B) -> (B -> A)

def axiom_schemas():
    A = Formula('var', 'A')
    B = Formula('var', 'B')
    C = Formula('var', 'C')
    schemas = [
        Formula('imp', A, Formula('imp', B, A)),
        Formula('imp', Formula('imp', A, Formula('imp', B, C)),
                        Formula('imp', Formula('imp', A, B), Formula('imp', A, C))),
        Formula('imp', Formula('imp', Formula('not', A), Formula('not', B)),
                        Formula('imp', B, A)),
    ]
    return schemas

def substitute(formula, mapping):
    if formula.kind == 'var' and formula.name in mapping:
        return mapping[formula.name]
    if formula.kind == 'var':
        return Formula('var', formula.name)
    if formula.kind == 'not':
        return Formula('not', substitute(formula.child, mapping))
    return Formula(formula.kind, substitute(formula.left, mapping), substitute(formula.right, mapping))

def all_axiom_instances(variables):
    schemas = axiom_schemas()
    varlist = sorted(variables)
    # For each axiom schema, substitute all possible formulas for A, B, C
    # For n variables, generate all possible formulas up to a certain depth
    # For simplicity, use only variables and their negations and implications up to depth 2
    atoms = [Formula('var', v) for v in varlist]
    formulas = set(atoms)
    # Add negations
    formulas |= {Formula('not', f) for f in atoms}
    # Add implications between atoms and their negations
    for a, b in itertools.product(formulas, repeat=2):
        formulas.add(Formula('imp', a, b))
    # Now instantiate schemas
    instances = set()
    for schema in schemas:
        for A, B, C in itertools.product(formulas, repeat=3):
            mapping = {'A': A, 'B': B, 'C': C}
            inst = substitute(schema, mapping)
            instances.add(inst)
    return instances

def prove(assumptions, goal_str):
    goal = parse_formula(goal_str)
    assumption_formulas = [parse_formula(a) for a in assumptions]
    variables = set()
    for f in assumption_formulas:
        variables |= f.variables()
    variables |= goal.variables()
    axioms = all_axiom_instances(variables)
    known = set(axioms) | set(assumption_formulas)
    proof_sequence = []
    derivation = {}
    # For fast lookup for modus ponens
    implications = defaultdict(list)  # antecedent -> list of (implication_formula, consequent)
    for f in known:
        if f.kind == 'imp':
            implications[f.left].append((f, f.right))
    # Add all knowns to proof sequence
    for f in known:
        if f in axioms:
            derivation[f] = (None, 'Axiom')
        else:
            derivation[f] = (None, 'Assumption')
        proof_sequence.append(f)
    # Forward chaining with modus ponens
    added = True
    while added:
        added = False
        new_facts = set()
        for f in list(proof_sequence):
            # For each implication with antecedent f
            for imp, cons in implications.get(f, []):
                if cons not in known:
                    known.add(cons)
                    proof_sequence.append(cons)
                    derivation[cons] = (f, imp)
                    # If cons is an implication, add to implications
                    if cons.kind == 'imp':
                        implications[cons.left].append((cons, cons.right))
                    added = True
                    if cons == goal:
                        return proof_sequence, derivation, goal
    return proof_sequence, derivation, goal

def format_proof(seq, deriv, goal):
    lines = []
    for i, f in enumerate(seq, 1):
        if deriv[f][0] is None:
            rule = deriv[f][1]
        else:
            ant, imp = deriv[f]
            rule = f"Modus Ponens from {seq.index(ant)+1} and {seq.index(imp)+1}"
        lines.append(f"{i}. {f}   ({rule})")
    if goal not in deriv:
        lines.append("Goal not derivable.")
    return "\n".join(lines)

def main():
    print("Hilbert-style Propositional Theorem Prover (Implication, Negation)")
    assumptions = input("Enter assumptions (comma-separated): ").split(',')
    assumptions = [a.strip() for a in assumptions if a.strip()]
    goal = input("Enter goal formula: ").strip()
    seq, deriv, goal_formula = prove(assumptions, goal)
    print("\nProof sequence:\n")
    print(format_proof(seq, deriv, goal_formula))
    if goal_formula in deriv:
        print("\nGoal is derivable!")
    else:
        print("\nGoal is NOT derivable.")

if __name__ == "__main__":
    main()