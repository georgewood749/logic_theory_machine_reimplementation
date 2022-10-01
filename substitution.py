from itertools import groupby
from theorems import axioms

CONNECTIVES = ["v", ".v.", ">", ".>.", ":>:"]

# Method of Substitution (MSb)
# # SIMILARITY TEST - CSm
# # # EXPRESSION DESCRIPTION - CSm(D)


def count_levels(expression):
    """Counts the total number of levels in the expression."""

    # Function returns the criteria for splitting the expression into each 'level'.
    def split_conditions(x):
        return x in CONNECTIVES

    # Divides list into groups based on the criteria returned from split_conditions function.
    group = groupby(expression, key=split_conditions)

    # Each list is stored in a dictionary.
    result = dict(enumerate((list(j) for i, j in group if not i)))

    # The length of the dictionary is returned to count the number of levels in the expression.
    nk = len(result)
    return nk


def count_distinct(expression):
    """Counts the total number of distinct variables in the expression."""

    # Temporary list created to allow list items to be updated.
    temp_list = []

    # Iterate through list to remove any connectives, leaving just the variables.
    for n in expression:
        temp_list.append(cancel_negative(n))
        if n in CONNECTIVES:
            temp_list.remove(n)

    # Distinct variables list updated to reflect new temp list, showing only variables.
    expression = temp_list

    # Set function is used to remove any duplicates in the expression list.
    exp_set = set(expression)

    # Length function used to calculate the number of distinct variables
    nj = len(exp_set)

    return nj


def count_variables(expression):
    """Counts the total number of variables in the expression."""

    # All connectives are removed from the list, leaving just the variables.
    for i in expression:
        if i in CONNECTIVES:
            expression.remove(i)

    # Length of the updated list is returned to show the total number of variables in the expression.
    nh = len(expression)
    return nh


def cancel_negative(n):
    """Removes the negative sign attached to a variable to allow accuracy when counting distinct variables."""

    # The leading strip method has been used to remove the first character of the variable string, if it is a minus.
    remove = '-'
    n = n.lstrip(remove)
    return n


def description(expression):
    """Returns description of the expression based on NK, NJ, NH."""
    levels = count_levels(expression)
    distinct = count_distinct(expression)
    variables = count_variables(expression)

    # Returns the description of the expression as a tuple.
    d = (levels, distinct, variables)
    return d


def description_left(expression):
    """Description of the left side of the expression in terms of NK, NJ and NH."""

    # Function used to set the criteria for splitting the expression into two sides.
    def split_conditions(x):
        return x in {":>:"}

    # Two sides of the expression is placed into a dictionary.
    group = groupby(expression, key=split_conditions)
    result = dict(enumerate((list(j) for i, j in group if not i)))

    # Description of expression returned as a tuple.
    dl = description(result[0])
    return dl


def description_right(expression):
    """Description of the right side of the expression using NK, NJ and NH."""

    # Function used to set the criteria for splitting the expression into two sides.
    def split_conditions(x):
        return x in {":>:"}

    group = groupby(expression, key=split_conditions)
    result = dict(enumerate((list(j) for i, j in group if not i)))

    # Description of expression returned as a tuple.
    dr = description(result[1])
    return dr


# # # DESCRIPTION COMPARISON - CSm(CD)

def compare_left_descriptions(expression):
    """Compares the left-hand side of the expression to be proved to the left-hand side of the axioms"""
    dl = description_left(expression)

    # List created to record which axioms/theorems match the DL for the expression.
    matches = []

    # Iterates through each axiom, if the DL of the expression matches that of the axiom, axiom is added to list.
    # Continue keyword used to allow function to continue searching after a match has already been found.
    for n in axioms:
        if dl == description_left(axioms[n]):
            matches.append(n)
        continue

    return matches


def compare_right_descriptions(expression):
    """Compares the left-hand side of the expression to be proved to the left-hand side of the axioms"""
    dr = description_right(expression)

    # List created to record which axioms/theorems match the DR for the expression.
    matches = []

    # Iterates through each axiom, if the DR of the expression matches that of the axiom, axiom is added to list.
    # Continue keyword used to allow function to continue searching after a match has already been found.
    for n in axioms:
        if dr == description_right(axioms[n]):
            matches.append(n)
        continue

    return matches


def test_similarity(expression):
    """Test for similarity between expression to be proved and saved theorems. Returns list of any matches"""

    # Calls the left and right side comparisons and checks if there are any axioms that have matching descriptions on
    # both sides. returns the key for the axiom if one is found, or false if not.
    left = compare_left_descriptions(expression)
    right = compare_right_descriptions(expression)
    matches = set(left).intersection(right)
    match_list = list(matches)

    # Checks that at least one axiom was matched to the expression.
    if len(matches) > 0:
        return match_list
    else:
        return False


# # MATCHING ROUTINE


def enumerate_expression(expression):
    """Converts expression list into an enumerated dictionary, to allow iteration through expression using the index."""
    enumerated_dict = {}
    for index, variable in enumerate(expression):
        enumerated_dict[index] = variable
    return enumerated_dict


def replacement_or(expression):
    """Replaces the connective v with the connective >. The variable before the connective is made negative.
    I.e: '-p v q' becomes 'p > q'. """
    enumerated_expression = enumerate_expression(expression)
    replaced_expression = []
    for i in enumerated_expression:
        if enumerated_expression[i] == "v":
            enumerated_expression[i] = ">"
            if not enumerated_expression[i - 1].startswith("-"):
                enumerated_expression[i - 1] = f"-{enumerated_expression[i - 1]}"
            else:
                enumerated_expression[i - 1] = enumerated_expression[i - 1].lstrip("-")

    for i in enumerated_expression:
        replaced_expression.append(enumerated_expression[i])
    return replaced_expression


def replacement_implies(expression):
    """Replaces the connective > with the connective v. The variable before the connective is made negative.
    I.e: 'p > q' becomes '-p v q'."""
    enumerated_expression = enumerate_expression(expression)
    replaced_expression = []
    for i in enumerated_expression:
        if enumerated_expression[i] == "v":
            enumerated_expression[i] = ">"
            if not enumerated_expression[i - 1].startswith("-"):
                enumerated_expression[i - 1] = f"-{enumerated_expression[i - 1]}"
            else:
                enumerated_expression[i - 1] = enumerated_expression[i - 1].lstrip("-")
    for i in enumerated_expression:
        replaced_expression.append(enumerated_expression[i])
    return replaced_expression


def matching(expression, axiom):
    """Matching routine. Made up of the substitute function and the replacement function. First the replacement method
    is used to match the connectives in the axiom and expression, if not already the same. Then the substitute method
    is called to match any non-identical variables. """

    enumerated_axiom = enumerate_expression(axiom)
    for i in enumerated_axiom:
        if enumerated_axiom[i] == "v" and "v" not in expression:
            axiom = replacement_or(axiom)

        elif enumerated_axiom[i] == ">" and ">" not in expression:
            axiom = replacement_implies(axiom)

    axiom = substitute(expression, axiom)

    return axiom


def substitute(expression, axiom):
    """Function substitutes all occurrences of a variable for another variable. I.e., any instances of p will be
    subbed for q. """

    # Axiom and expression are enumerated to allow iteration through each list.
    enumerated_expression = enumerate_expression(expression)
    enumerated_axiom = enumerate_expression(axiom)

    # New list created for the matched axiom, and empty dictionary created to act as a key for substituted variables.
    matched_axiom = []
    subbed_variables_key = {}

    # Axiom is iterated through to check if the variables in the axiom match those in the expression. If they do not
    # match, the variable must be substituted. This list stores the variable that has been substituted as the key and
    # the variable that it is being substituted for as the value.
    for i in enumerated_axiom:
        if enumerated_axiom[i] not in CONNECTIVES and enumerated_axiom[i] != enumerated_expression[i]:
            subbed_variables_key[enumerated_axiom[i]] = enumerated_expression[i]

    # The enumerated axiom is looped through, to check: 1) if the variable is a connective (if so, it is added to the
    # matched axiom list unchanged). 2) if the axiom variable is different to that of the expression (if so,
    # the matched axiom is appended with the value linked to the key of the variable).
    # If the variable in the axiom is the same as that in the expression, it is added unchanged to the matched axiom.
    for i in enumerated_axiom:
        if enumerated_axiom[i] in CONNECTIVES:
            matched_axiom.append(enumerated_axiom[i])

        elif enumerated_axiom[i] != enumerated_expression[i]:
            matched_axiom.append(subbed_variables_key[enumerated_axiom[i]])

        else:
            matched_axiom.append(enumerated_expression[i])

    # The substituted axiom is returned after the substitutions have been made. I.e. any instances of p have been
    # changed to q if the expression has q where the axiom has a p.
    return matched_axiom


def report_identical(expression, axiom):
    """Reports successful termination of matching routine, or reports failure if expression and axiom cannot be
    matched. """
    if expression == axiom:
        return True
    elif not axiom:
        return False
    else:
        return False


def method_of_substitution(expression):
    """Method of substitution is made up of the similarity check and the matching routine"""
    similar_axioms = test_similarity(expression)
    if not similar_axioms:
        print("There are no axioms with identical left and right sides to the expression.")
        return False
    else:
        print(f"Axiom(s) {similar_axioms} have identical left and right descriptions to the expression.")
        axiom_key = sorted(test_similarity(expression))
        if axiom_key:
            axiom = axioms[axiom_key[0]]
            print(f"Axiom {axiom_key[0]}    : ! {axiom}")
            print(f"Expression : ? {expression}")
            axiom = matching(expression, axiom)

        else:
            axiom = False

    identical = report_identical(expression, axiom)
    if identical:
        print(f"Expression has been matched to axiom {axiom_key[0]}.")
        return axiom
    else:
        print("Expression could not be matched.")
        return False
