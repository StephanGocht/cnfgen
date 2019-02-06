import cnfformula.encoding.constructs as fe
import math

import cnfformula.cnf as cnf
from collections import deque

from cnfformula.cmdline  import register_cnf_transformation_subcommand
from cnfformula.transformations import register_cnf_transformation

headerInfo = """
Requires fork by Stephan Gocht:
https://github.com/StephanGocht/cnfgen

"""

@register_cnf_transformation
def cardinality2CnfWithHelper(orig, transform = None):
    """
    Transforms all cardinality constraitns to clauses, but introduces
    helper variables that allow recovering the cardinality constraint.
    """
    f = fe.fromCNFgen(orig)
    visitor = RecursiveTransformVisitor(transform)
    transformed = visitor.visit(f)
    print(fe.toString(transformed))
    newF = cnf.CNF(header = orig.header + headerInfo)
    newF.mode_default()
    fe.toCNFgen(newF, transformed)
    return newF

@register_cnf_transformation_subcommand
class TramsformCmd:
    name='cardinality2CnfWithHelper'
    description="""
    Transforms all cardinality constraitns to clauses, but introduces
    helper variables that allow recovering the cardinality constraint."""

    @staticmethod
    def setup_command_line(parser):
        parser.description = TramsformCmd.description + """\n\n The options set the mode for base case,
            where all remaining clauses can be added directly, only followed by one division."""
        g = parser.add_mutually_exclusive_group()
        g.add_argument('--input','-i',
                            action='store_true',
                            default=False,
                            help="Allow adding all constraints to one base constraint (kind of input generalized-resolution).")
        g.add_argument('--tree','-t',
                            action='store_true',
                            default=False,
                            help="Add constraints in form of a tree.")
        g.add_argument('--tree_reuse','-r',
                            action='store_true',
                            default=False,
                            help="Add constraints in form of a tree and reuse variables in leaf nodes.")

    @staticmethod
    def transform_cnf(F,args):
        if args.tree:
            return cardinality2CnfWithHelper(F, TransformToCNFWithRecoveryTree())
        elif args.tree_reuse:
            return cardinality2CnfWithHelper(F, TransformToCNFWithRecoveryTreeWithReuse())
        else:
            return cardinality2CnfWithHelper(F)


class RecursiveTransformVisitor(fe.Visitor):
    def __init__(self, transform = None):
        # important to have this in the constructor, as otherwise
        # the same helper variables will be generated over and over again
        self.transform = transform
        if self.transform is None:
            self.transform = TransformToCNFWithRecovery()

    def genericVisit(self, x):
        return x

    def visit_Inequality(self, ineq):
        f = ineq.normalizedCoefficients()
        for a,x in f.terms:
            if a != 1:
                return ineq

        if f.rhs > 0:
            return self.transform(f)
        else:
            return ineq

    def visit_And(self, conjunction):
        result = fe.And()
        for x in conjunction:
            result.append(self.visit(x))
        return result

def nCr(n,r):
    f = math.factorial
    return f(n) // f(r) // f(n-r)


class SimpleHelperVarGenerator:
    def __init__(self, prefix = "z"):
        self._numHelper = 0
        self.prefix = prefix

    def __call__(self):
        self._numHelper += 1
        return "%s_%i"%(self.prefix, self._numHelper)


class TransformToCNFWithRecovery:
    def __init__(self, helperVariableGenerator = None):
        self.getFreshVariable = helperVariableGenerator
        if self.getFreshVariable is None:
            self.getFreshVariable = SimpleHelperVarGenerator()

    def cancelationTerms(self, k):
        """
        return k lists of terms such that it is possible to add the
        lists in a way that always one variable cancles and adding
        all terms together yields 0
        """
        variables = [self.getFreshVariable() for i in range(k - 1)]
        result = list()
        result.append([(1, x) for x in variables])
        result.extend([[(-1,x)] for x in variables])
        return result

    def __call__(self, f):
        f = f.normalizedCoefficients()
        for a,x in f.terms:
            if a != 1:
                raise ValueError("Can only transform cardinality constraints (all coefficients 1).")

        return self._recurse([x for a,x in f.terms], f.rhs)

    def _plainAdded(self, lits, bound):
        assert(len(lits) >= bound)
        assert(bound > 0)

        if bound == 1 or len(lits) == bound:
            return (1, bound)
        else:
            n = len(lits)
            r = len(lits) - bound + 1
            rhs = nCr(n, r)
            coeffs = nCr(n - 1, r - 1)
            return (coeffs, rhs)

    def _canBeAddedPlain(self, coeffs, rhs, bound):
        return math.ceil(rhs / coeffs) == bound

    def _baseCase(self, lits, bound, implicationVars):
        coeffs, rhs = self._plainAdded(lits, bound)
        if self._canBeAddedPlain(coeffs, rhs, bound):
            # we can just add all clauses of the right size
            ineq = fe.GEQ([(1,x) for x in lits], bound)

            clauses = fe.transformToCNF(ineq)
            clauses = fe.And([fe.GEQ([(1,x) for x in c], 1) for c in clauses])

            # add hint on the divisor for testing
            clauses.divisor = coeffs

            numClauses = len(clauses)

            for a,x in implicationVars:
                if a == bound:
                    # small trick for nicer looking constraints. While this
                    # will not sum up to divisor * a it will still be a after
                    # division and rounding up
                    r = 0
                    value = 1
                else:
                    # summing everything up should yield divisor * a
                    afterSum = abs(a) * clauses.divisor
                    r = afterSum % numClauses
                    value = afterSum // numClauses

                for c in clauses:
                    if r > 0:
                        coeff = value + 1
                        r -= 1
                    else:
                        coeff = value
                    coeff = int(math.copysign(coeff, a))
                    if coeff != 0:
                        c.terms.append((coeff, x))

            # add vars for cancelation
            cancel = self.cancelationTerms(numClauses)
            for clause, extension in zip(clauses, cancel):
                clause.terms.extend(extension)

            return clauses
        else:
            return None

    def _recurse(self, lits, bound, implicationVars = []):
        r"""
            :param lits: :math:`L`
            :param bound: :math:`b`
            :param implicationVars: :math:`I`

            creates constraints that can derive

            .. math::
                \sum_{(a,x) \in I} ax + \sum_{x \in L} x \geq b

            by cancelling addition and can be restricted to
            clauses implying

            .. math::
                \sum_{x \in L} x \geq b
        """

        c = self._baseCase(lits, bound, implicationVars)
        if c is not None:
            return c
        else:
            result = fe.And()

            head, tail = lits[-1], lits[:-1]

            helperVariable = self.getFreshVariable()

            # head is true
            result.append(self._recurse(tail, bound - 1,
                [(min(a, bound - 1),x) for a,x in implicationVars] + [(1, helperVariable)]))

            # head is false
            result.append(self._recurse(tail, bound,
                [(bound, head)] + implicationVars + [(-bound + 1, helperVariable)]))

            # adding both constraints, such that the new helper variable cancels will yield
            # \sum_{(a,x) \in I} bax + \sum_{x \in L} bx \geq (b - 1)*(b - 1) + b
            # \sum_{(a,x) \in I} bax + \sum_{x \in L} bx \geq b * b - b + 1
            # division by b will yield
            # \sum_{(a,x) \in I} ax + \sum_{x \in L} x \geq b


            # add hint on the divisor for testing
            result.divisor = bound
            return result

class TransformToCNFWithRecoveryTree(TransformToCNFWithRecovery):
    def cancelationTerms(self, k):
        hight = math.ceil(math.log2(k))
        leafLayer = 2**hight
        empty = leafLayer - 2 * (k - leafLayer // 2)
        fullTree = 2 * leafLayer - 1
        numHelper = fullTree - empty - k
        variables = [self.getFreshVariable() for i in range(numHelper)]

        def parent(i):
            return (i-1)//2

        result = list()
        for i in range(k):
            node = len(variables) + i
            isLastLayer = math.floor(math.log2(node + 1)) == hight
            line = list()
            while node != 0:
                isLeft = node % 2 == 1
                coeff = 1 if isLeft else -1
                if not isLastLayer:
                    coeff *= 2
                node = parent(node)
                line.append((coeff, variables[node]))
            result.append(line)
        return result

class TransformToCNFWithRecoveryTreeWithReuse(TransformToCNFWithRecovery):
    def cancelationTerms(self, k):
        hight = math.ceil(math.log2(k))
        leafLayer = 2**hight
        empty = leafLayer - 2 * (k - leafLayer // 2)
        fullTree = 2 * leafLayer - 1
        numHelper = fullTree - empty - k


        variables = [[self.getFreshVariable()] * (2**i) for i in range(math.ceil(math.log2(numHelper)) + 1)]
        print(variables)
        variables = sum(variables,[])[:numHelper]
        print(numHelper)
        print(variables)

        def parent(i):
            return (i-1)//2

        result = list()
        for i in range(k):
            node = len(variables) + i
            isLastLayer = math.floor(math.log2(node + 1)) == hight
            line = list()
            while node != 0:
                isLeft = node % 2 == 1
                coeff = 1 if isLeft else -1
                if not isLastLayer:
                    coeff *= 2
                node = parent(node)
                line.append((coeff, variables[node]))
            result.append(line)
        return result

class NoCancelation(ValueError):
    pass

def findCancelationFactors(ineq1, ineq2):
    ineq1 = ineq1.normalizedVariables()
    ineq2 = ineq2.normalizedVariables()

    data = dict()
    for a,x in ineq1.terms:
        data[x] = a

    for a,x in ineq2.terms:
        if x in data:
            if (data[x] > 0) != (a > 0):
                return (abs(a), abs(data[x]))

    raise NoCancelation()

class DisplayResult(fe.Visitor):
    def __init__(self):
        self.depth = -1

    def genericVisit(self, x):
        raise TypeError()

    def visit_Inequality(self, ineq):
        print("  "*self.depth, fe.toString(ineq))
        return ineq

    def visit_And(self, conjunction):
        print("  "*self.depth, "{")
        self.depth += 1
        divisor = 0
        todo = deque(self.visit(f) for f in conjunction)
        s = todo.popleft()

        mark = None
        todo.append(mark)

        progress = False
        while len(todo) > 1:
            ns = todo.popleft()

            if (ns == mark):
                if (not progress):
                    raise NoCancelation()
                else:
                    progress = False
                    todo.append(ns)
            else:
                try:
                    a,b = findCancelationFactors(s, ns)
                except NoCancelation:
                    todo.append(ns)
                else:
                    s = a*s + b*ns
                    progress = True

        self.depth -= 1

        print("  "*self.depth,"}","=",fe.toString(s))

        try:
            divisor = conjunction.divisor
        except AttributeError:
            raise ValueError("This method only works when a hint is set for which divisor to use.")

        s = s / divisor
        s = s.normalizedVariables()
        print("  "*self.depth," ","/%i ="%(divisor),fe.toString(s))
        return(s)

def main():
    v = DisplayResult()
    transform = TransformToCNFWithRecoveryTree()
    f = fe.GEQ([(1, "x%i"%i) for i in range(4)], 2)
    # f = fe.LEQ([(1, "x%i"%i) for i in range(6)], 3)
    v.visit(transform(f))

if __name__ == '__main__':
    main()