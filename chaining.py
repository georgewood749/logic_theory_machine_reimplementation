from theorems import axioms
import substitution
import detachment


def similarity1(expression):
    """Search for a theorem (T) with a left side similar to the left side of expression (A)."""
    matches = []
    description_a_left = substitution.description_left(expression)
    for i in axioms:
        if substitution.description_left(axioms[i]) == description_a_left:
            matches.append(i)

    return matches


def similarity2(b):
    """Search for a theorem (T) with a left side similar to B"""
    matches = []
    description_b = substitution.description(b)
    for i in axioms:
        if substitution.description_left(axioms[i]) == description_b:
            matches.append(i)

    return matches


def construct_proof(a, c):
    """The proof for the expression is constructed using the previously calculated 'a' and 'c' values."""
    a_implies_c = []

    enumerated_a = substitution.enumerate_expression(a)
    enumerated_c = substitution.enumerate_expression(c)
    for i in enumerated_a:
        a_implies_c.append(enumerated_a[i])

    a_implies_c.append(":>:")

    for i in enumerated_c:
        a_implies_c.append(enumerated_c[i])

    return a_implies_c


def method_of_chaining(expression):
    """Forward chaining method. To try to prove A>C, we must first prove A>B and B>C."""
    print(f"A>C: {expression}")

    similar_theorems = similarity1(expression)
    b = detachment.get_right_subexpression(axioms[similar_theorems[-1]])

    a_b = axioms[similar_theorems[-1]]
    print(f"A>B: {a_b}")

    c = detachment.get_right_subexpression(expression)
    description_c = substitution.description(c)

    similar_theorems2 = similarity2(b)
    similar_theorems3 = []
    for i in similar_theorems2:
        if substitution.description_right(axioms[i]) == description_c:
            similar_theorems3.append(i)

    b_c = axioms[similar_theorems3[0]]
    print(f"B>C: {b_c}")

    a_b_left = detachment.get_left_subexpression(a_b)
    b_c_right = detachment.get_right_subexpression(b_c)

    if len(similar_theorems3) > 0:

        proof = construct_proof(a_b_left, b_c_right)
        print(f"A>C: {proof}")

        if proof == expression:
            return proof
        else:
            return False
    else:
        return False
