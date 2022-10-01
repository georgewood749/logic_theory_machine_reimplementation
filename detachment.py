from itertools import groupby
from theorems import axioms
import substitution

CONNECTIVES = ["v", ".v.", ">", ".>.", ":>:"]


def similarity(expression):
    """Attempts to find any axioms or theorems with right-side description identical to the description of the whole
    expression."""
    # The description function from substitution.py is called and saved as the variable expression_d.
    # This is then checked against the right description
    expression_d = substitution.description(expression)
    for i in axioms:
        if substitution.description_right(axioms[i]) == expression_d:
            print(f"Found similar axiom: {axioms[i]}")
            return axioms[i]
        else:
            print("Could not find any axioms with a right description identical to description of the expression.")
            return False


def separate_units(expression):
    """Separates the expression into units to allow for contraction."""
    # Expression is enumerated to allow iteration through each element.
    enumerated_expression = substitution.enumerate_expression(expression)
    connective_list = []
    for i in enumerated_expression:
        if enumerated_expression[i] == ":>:" or enumerated_expression[i] == ".v." or enumerated_expression[i] == ".>.":
            connective_list.append(enumerated_expression[i])

    # The split_condition function from the description portions of the substitution method has been used again to
    # separate the expression into units that can be used in the contraction function below.
    def split_conditions(x):
        return x in {":>:", ".v.", ".>."}

    group = groupby(expression, key=split_conditions)
    result = dict(enumerate((list(j) for i, j in group if not i)))

    unit_list = []

    # The result dictionary is iterated through to create a list of the units in the expression. In the case of this
    # program, a unit will be distinguished by a connective surrounded by dots (i.e: ".>. or ".v.", and the main
    # connective ":>:".
    for i in result:
        expression_units = "".join(result[i])
        unit_list.append(expression_units)

    new_list = []

    # Zip function is called to iterate through both the unit list and the connective list. This allows a new list to
    # be created, by inserting the first unit, then the first connective etc., until the connective list has been
    # exhausted.
    for (a, b) in zip(unit_list, connective_list):
        new_list.append(a)
        new_list.append(b)

    # As there will always be one more unit than connective, the final unit is added to the end of the new list after
    # the zip function exhausts the connective list.
    new_list.append(unit_list[-1])

    expression = new_list
    return expression


def contraction(expression):
    """Contracts the units in the expression to a more simplified form."""
    # A list of variables has been created to swap to in the contraction function.
    alphabet = ['a', 'b', 'c', 'p', 'q', 'r', 'A', 'B', 'C', 'P', 'Q', 'R']

    # Expression is enumerated to allow iteration through list.
    enumerated_expression = substitution.enumerate_expression(expression)
    new_dict = {}

    # the variable 'i' has been used to iterate through each element of the expression in the while loop.
    i = 0

    # j is used to assign each unit a contracted value in the order of the alphabet list above, rather than using i,
    # which would skip values in the list for any connective in the expression.
    j = 0

    # While loop to iterate through each element in the expression. If the element is not a connective,
    # it is contracted to one of the values in the alphabet list above and appended to the new list.
    # If the element is a connective, it is simply added into the new list.
    while i < len(enumerated_expression):
        if enumerated_expression[i] not in CONNECTIVES:
            new_dict[alphabet[j]] = enumerated_expression[i]
            j += 1
        else:
            new_dict[i] = enumerated_expression[i]
        i += 1

    # New list created for the new contracted expression, rather than storing the contracted variables in a dictionary.
    contracted_expression = []

    # Iterates through each key in the dictionary, and checks if it is a string (and therefore a contracted value),
    # or an integer (and therefore a connective). If the key is string, it adds the key (i.e. the contracted unit) to
    # the contracted expression. Else, if the key is an integer, the value is added to the contracted expression.
    # Hence, we are left with the fully contracted expression, with the connectives being left untouched for now.
    for key in new_dict.keys():
        if isinstance(key, str):
            contracted_expression.append(key)
        elif isinstance(key, int):
            contracted_expression.append(new_dict[key])

    # Returns both the contracted expression, and the new dictionary as a tuple, allowing the new dictionary to be
    # used as a key for reverse contraction later.
    return contracted_expression, new_dict


def standardise_expression(expression):
    """Standardises a contracted expression, changing any '.>.' or '.v.' connectives to the standard 'v' or '>'
    connectives."""
    standardised_exp = []
    enumerated_expression = substitution.enumerate_expression(expression)

    for i in enumerated_expression:
        if enumerated_expression[i] == ".>.":
            standardised_exp.append('>')
        elif enumerated_expression[i] == ".v.":
            standardised_exp.append('v')
        else:
            standardised_exp.append(enumerated_expression[i])

    return standardised_exp


def standardise_subexpression(expression):
    """Standardises a sub-expression, changing it to the form of a standard expression. I.e., changing any .>. to :>:"""
    standardised_exp = []
    enumerated_expression = substitution.enumerate_expression(expression)

    for i in enumerated_expression:
        if enumerated_expression[i] == ".>.":
            standardised_exp.append(':>:')
        else:
            standardised_exp.append(enumerated_expression[i])

    return standardised_exp


def get_left_subexpression(expression):
    """Breaks down the expression entered into whatever sub-expressions it is made up of. Allows comparison of
    descriptions."""

    def split_conditions(x):
        return x in {":>:"}

    group = groupby(expression, key=split_conditions)
    result = dict(enumerate((list(j) for i, j in group if not i)))

    return result[0]


def get_right_subexpression(expression):
    """Breaks down the expression entered into whatever sub-expressions it is made up of. Allows comparison of
    descriptions."""

    def split_conditions(x):
        return x in {":>:"}

    group = groupby(expression, key=split_conditions)
    result = dict(enumerate((list(j) for i, j in group if not i)))

    return result[1]


def method_of_detachment(expression):
    """Uses the key created in the contraction method to update the variables in the axiom to match the contracted
    values in the contracted expression."""

    # Expression is broken down into each unit, and then contracted using the contraction method above.
    units = separate_units(expression)
    contracted_expression = contraction(units)[0]

    # Contraction key is returned from the contraction function, this allows the matched similar axioms to be
    # contracted using the same new variables.
    contraction_key = contraction(units)[1]

    standardised_expression = standardise_expression(contracted_expression)

    dl = substitution.description_left(standardised_expression)
    dr = substitution.description_right(standardised_expression)

    # The right-hand side of each of the theorems/axioms in memory is entered into a new dictionary
    right_subexpressions = {}
    for i in axioms:
        right_subexpressions[i] = get_right_subexpression(axioms[i])

    # The dictionary of each of the right-hand sides is further filtered to only include those that have a 'main'
    # connective, and are therefore treated as whole expressions.
    filtered_right_subs = {}
    for i in right_subexpressions:
        if ".v." in right_subexpressions[i] or ".>." in right_subexpressions[i]:
            filtered_right_subs[i] = right_subexpressions[i]

    # Each of the subexpressions are standardised, and rewritten as expressions with standard connectives (i.e.,
    # '>' or 'v'), and saved in a new dictionary.
    standardised_subexpressions = {}
    for i in filtered_right_subs:
        standardised_subexpressions[i] = standardise_subexpression(filtered_right_subs[i])

    # The right and left descriptions of each of the subexpressions are added into two new dictionaries, allowing for
    # the matched axiom to be compared to each individual subexpression.
    right_sub_drs = {}
    right_sub_dls = {}
    for i in standardised_subexpressions:
        if ":>:" in standardised_subexpressions[i]:
            right_sub_dls[i] = substitution.description_left(standardised_subexpressions[i])
            right_sub_drs[i] = substitution.description_right(standardised_subexpressions[i])

    # A list is created to store any matches for the left and right descriptions of the axiom.
    dl_match = []
    dr_match = []

    for i in right_sub_dls:
        if right_sub_dls[i] == dl:
            dl_match.append(i)

    for i in right_sub_drs:
        if right_sub_drs[i] == dr:
            dr_match.append(i)

    # A variable is created to show what axioms in the theorem memory have identical right and left descriptions to
    # the right subexpression of the expression to be proved.
    similar_axiom_key = False

    # Each list is traversed to check if there is an axiom that appears in both match lists. If there is one,
    # the similar_axiom_key is updated to this axiom.
    for x in dl_match:
        for y in dr_match:
            if x == y:
                similar_axiom_key = x

    # A variable is created to store the similar axiom, by using the key of the axiom found in the above code.
    if similar_axiom_key:
        similar_axiom = axioms[similar_axiom_key]
        # The axiom is broken down into just the subexpression on the right-hand side of the main connective. Then it is
        # enumerated to allow for iteration through each element.
        axiom_right = get_right_subexpression(similar_axiom)
        enumerated_axiom_right = substitution.enumerate_expression(axiom_right)

        # A new list is created to store the matched axiom after the reverse contraction has been applied, using the
        # contraction key.
        enumerated_similar_axiom = substitution.enumerate_expression(similar_axiom)
        matched_axiom = []

        for i in enumerated_similar_axiom:
            if enumerated_similar_axiom[i] in contraction_key.keys():
                matched_axiom.append(contraction_key[enumerated_similar_axiom[i]])
            else:
                matched_axiom.append(enumerated_similar_axiom[i])

        # A new list is created to store the matched axiom's right subexpression after the reverse contraction has been
        # applied, using the contraction key.
        matched_axiom_right = []
        for i in enumerated_axiom_right:
            if enumerated_axiom_right[i] in contraction_key.keys():
                matched_axiom_right.append(contraction_key[enumerated_axiom_right[i]])
            else:
                matched_axiom_right.append(enumerated_axiom_right[i])

        # Must prove that left side of matched_axiom_right
        expanded_axiom = []

        enumerated_matched_axiom = substitution.enumerate_expression(matched_axiom)

        def split_var(var):
            return [char for char in var]

        for i in enumerated_matched_axiom:
            if enumerated_matched_axiom[i] not in CONNECTIVES:
                characters = split_var(enumerated_matched_axiom[i])
                for x in characters:
                    expanded_axiom.append(x)
            else:
                expanded_axiom.append(enumerated_matched_axiom[i])

        expanded_axiom_left = get_left_subexpression(expanded_axiom)

        enumerated_expanded_axiom_left = substitution.enumerate_expression(expanded_axiom_left)
        for i in enumerated_expanded_axiom_left:
            if enumerated_expanded_axiom_left[i] == ".>.":
                enumerated_expanded_axiom_left[i] = ":>:"
            expanded_axiom_left = []
            for x in enumerated_expanded_axiom_left:
                expanded_axiom_left.append(enumerated_expanded_axiom_left[x])

        print(f"? Expression'': {expanded_axiom_left}")
        print(f"! Axiom {similar_axiom_key}: {similar_axiom}")

        proof = substitution.substitute(similar_axiom, enumerated_expanded_axiom_left)
        print(f"Proof for expression'': {proof}")
        return proof

    else:
        print("No similar axioms could be found.")
        return False

    # First run similarity check to see if there are any axioms with a right side description that matches the
    # description of the entire expression. If one is found, apply the matching routine to the right side of the
    # axiom and the expression. If matching is successful, we apply the method of substitution on the left side of
    # this expression.

    # If no similar theorem could be found, run the contraction method to simplify the expression.
