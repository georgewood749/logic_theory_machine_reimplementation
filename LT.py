import substitution
import detachment
import chaining
from theorems import axioms


def executive_routine(expression):
    sub = substitution.method_of_substitution(expression)
    if sub:
        print("Expression has been proved using the method of substitution.\n")
        axioms.update({(len(axioms) + 1): sub})

    else:
        print("Expression could not be proved using the method of substitution.\n")
        print("LT will now attempt to prove the expression using the method of detachment.")

        detach = detachment.method_of_detachment(expression)
        if detach:
            print("Expression has been proved using the method of detachment.\n")
            axioms.update({(len(axioms) + 1): detach})

        else:
            print("Expression could not be proved using the method of detachment.\n")
            print("LT will now attempt to prove the expression using the method of chaining.")

            chain = chaining.method_of_chaining(expression)
            if chain:
                print("Expression has been proved using the method of chaining.\n")
                axioms.update({(len(axioms) + 1): chain})

            else:
                print("\nExpression could not be proved using the methods of LT.\n")


loop = True
while loop:
    expression_input = input("\nPlease enter an expression to be proved.\n"
                             "Enter the central connective as ':>:'. \n"
                             "Units can be defined by using '.>.' or '.v.' connectives.\n"
                             "To close the program, enter 'quit'.\n"
                             "To see the list of theorems, enter 'theorems'.\n"
                             "> ")

    exp_list = expression_input.split(" ")
    if expression_input == "quit":
        loop = False
    elif expression_input == "theorems":
        for i in axioms:
            print(f"{i}: {axioms[i]}")
    else:
        executive_routine(exp_list)
