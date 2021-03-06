"""
Provides a more flexible way of encoding constraints.

Still in development.
Currently supports clauses and linear inequalities.
"""

import itertools
import sys

from math import ceil
import cnfformula.cnf as cnf

# a literal is anything hashable


class Visitor(object):
    def visit(self, node, *args, **kwargs):
        meth = None
        for cls in node.__class__.__mro__:
            meth_name = 'visit_' + cls.__name__
            meth = getattr(self, meth_name, None)
            if meth:
                break

        if not meth:
            meth = self.genericVisit
        return meth(node, *args, **kwargs)

    def genericVisit(self, x):
        raise NotImplementedError()


def join(klass, a, b):
    result = klass()
    if isinstance(a, klass):
        result.extend(a)
    else:
        result.append(a)

    if isinstance(b, klass):
        result.extend(b)
    else:
        result.append(b)

    return result


class OPTree:
    def __invert__(self):
        return negate(self)

    def __and__(self, other):
        return join(And, self, other)

    def __or__(self, other):
        return join(Or, self, other)

    def __radd__(self, other):
        return self + other

    def __add__(self, other):
        if other is 0:
            other = Sum()
        return join(Sum, self, other)

    def __rmul__(self, other):
        return self * other

    def __mul__(self, other):
        if other is 1:
            return self
        return join(Product, self, other)

    def __eq__(self, other):
        return (self <= other) & (self >= other)

    def __le__(self, other):
        return LEQ(*standardize(self, other))

    def __ge__(self, other):
        return GEQ(*standardize(self, other))

    def __lt__(self, other):
        return LT(*standardize(self, other))

    def __gt__(self, other):
        return GT(*standardize(self, other))

    def __neg__(self):
        return -1 * self

    def __rsub__(self, other):
        return other + (-self)

    def __sub__(self, other):
        return self + (-other)


def standardize(left, right):
    visitor = Convert2Terms()

    terms = visitor.visit(left)

    termsRight = visitor.visit(right)
    terms.extend([-coeff, var] for coeff, var in termsRight)

    const = sum([coeff for coeff, var in terms if var is None])
    const *= -1
    terms = [(coeff, var) for coeff, var in terms if var is not None]

    return terms, const


class Convert2Terms(Visitor):
    def genericVisit(self, x):
        if isinstance(x, int):
            return [(x, None)]
        else:
            return [(1, x)]

    def visit_Product(self, x):
        factor = 1
        var = None
        for y in x:
            if isinstance(y, int):
                factor *= y
            elif var is None:
                var = y
            else:
                raise RuntimeError(
                    "Trying to convert multiply with more than one non integer.")

        if isinstance(var, Sum):
            return [(factor * coeff, var) for coeff, var in self.visit(var)]
        else:
            return [(factor, var)]

    def visit_Sum(self, x):
        result = list()
        for y in x:
            result.extend(self.visit(y))
        return result


class Sum(OPTree, list):
    pass


class Product(OPTree, list):
    pass


class Term(OPTree, list):
    pass


class And(OPTree, list):
    pass


class Not(OPTree):
    def __init__(self, x):
        self.x = x


def negate(x):
    return normalizeNot(Not(x))


def normalizeNot(x):
    while (type(x) == Not and type(x.x) == Not):
        x = x.x.x
    return x


class Or(list, OPTree):
    pass


class Clause(Or, OPTree):
    pass


class Inequality(OPTree):
    """
    creates sum of terms greater equal rhs
    """

    def __init__(self, terms, rhs):
        self.terms = terms
        for a, x in self.terms:
            if not isinstance(a, int):
                raise TypeError("Coefficient is not an integer.")
        self.rhs = rhs

    def normalizedCoefficients(self):
        """
        return inequality that does not contain negative coefficients
        """
        normalizedTerms = list()
        normalizedDegree = self.rhs

        for a, x in self.terms:
            if a < 0:
                a *= -1
                x = negate(x)
                normalizedDegree += a
            normalizedTerms.append((a, x))

        return Inequality(normalizedTerms, normalizedDegree)

    def normalizedVariables(self):
        """
        return inequality that does not contain negated variables
        """
        normalizedTerms = list()
        normalizedDegree = self.rhs

        for a, x in self.terms:
            x = normalizeNot(x)
            if type(x) == Not:
                a *= -1
                x = negate(x)
                normalizedDegree += a
            normalizedTerms.append((a, x))

        return Inequality(normalizedTerms, normalizedDegree)

    def isCardinality(self):
        for a, x in self.terms:
            if a < -1 or a > 1:
                return False
        return True

    def __add__(self, otherIneq):
        ineq1 = self.normalizedVariables()
        ineq2 = otherIneq.normalizedVariables()

        data = dict()
        for a, x in ineq1.terms:
            data[x] = a

        for a, x in ineq2.terms:
            if x in data:
                data[x] += a
            else:
                data[x] = a

        terms = [(data[x], x) for x in sorted(data.keys()) if data[x] != 0]
        return Inequality(terms, ineq1.rhs + ineq2.rhs)

    def __truediv__(self, f):
        ineq = self.normalizedCoefficients()
        return Inequality([(ceil(a/f), x) for a, x in ineq.terms], ceil(ineq.rhs/f))

    def __rmul__(self, f):
        return Inequality([(f * a, x) for a, x in self.terms], f * self.rhs)


class LEQ(Inequality):
    def __init__(self, terms, rhs):
        super().__init__([(-a, x) for a, x in terms], -rhs)


class GEQ(Inequality):
    pass


class GT(GEQ):
    def __init__(self, terms, rhs):
        super().__init__(terms, rhs + 1)


class LT(LEQ):
    def __init__(self, terms, rhs):
        super().__init__(terms, rhs - 1)


def transformToCNF(something):
    t = TransformToCNF()
    t.visit(something)
    return t.result


class TransformToCNF(Visitor):
    def __init__(self):
        self.result = And()

    def visit_And(self, conjunction):
        for x in conjunction:
            self.visit(x)

    def visit_Or(self, disjunction):
        self.result.append(Clause(disjunction))

    def visit_Inequality(self, inequality):
        inequality = inequality.normalizedCoefficients()

        if inequality.isCardinality():
            lits = [x for a, x in inequality.terms if a != 0]
            for subset in itertools.combinations(lits, len(lits) - inequality.rhs + 1):
                self.result.append(Clause(subset))

        else:
            raise NotImplementedError(
                "Can only convert cardinality constraints")

    def visit_Clause(self, clause):
        self.result.append(clause)


def toString(x):
    v = PrintVisitor()
    return v.visit(x)


class PrintVisitor(Visitor):
    def genericVisit(self, x):
        return str(x)

    def visit_And(self, conjunction):
        s = ""
        for x in conjunction:
            s += self.visit(x) + "\n"
        return s

    def visit_Or(self, disjunction):
        return " ∨ ".join([self.visit(x) for x in disjunction])

    def visit_Inequality(self, inequality):
        s = ""
        s += " ".join(["%+d %s" % (a, self.visit(x))
                       for a, x in inequality.terms])
        s += " ≥ %d" % (inequality.rhs)
        return s

    def visit_Not(self, x):
        return "Not(%s)" % (self.visit(x.x))


def lit2CNFgenLit(l):
    l = normalizeNot(l)
    if type(l) == Not:
        return (False, l.x)
    else:
        return (True, l)


def intToLit(i):
    var = "x_%i" % (abs(i))
    if i < 0:
        return Not(var)
    else:
        return var


def fromCNFgen(cnst):
    if type(cnst) == cnf.CNF:
        result = And()
        for constraint in cnst._constraints:
            result.append(fromCNFgen(constraint))
        return result
    elif type(cnst) in [cnf.disj, cnf.xor]:
        result = And()
        for cls in cnst.clauses():
            result.append(GEQ([(1, intToLit(i)) for i in cls], 1))
        return result
    elif type(cnst) in [cnf.weighted_eq, cnf.weighted_geq]:
        terms = [(a, intToLit(x)) for a, x in cnst]
        if type(cnst) == weighted_eq:
            return And([GEQ(terms, cnst.value), LEQ(terms, cnst.value)])
        else:
            return GEQ(terms, cnst.value)
    elif type(cnst) in [cnf.eq, cnf.geq, cnf.greater, cnf.leq, cnf.less]:
        terms = [(1, intToLit(x)) for x in cnst]
        if type(cnst) == cnf.eq:
            return And([GEQ(terms, cnst.value), LEQ(terms, cnst.value)])

        elif type(cnst) == cnf.geq:
            return GEQ(terms, cnst.threshold)

        elif type(cnst) == cnf.greater:
            return GT(terms, cnst.threshold)

        elif type(cnst) == cnf.leq:
            return LEQ(terms, cnst.threshold)

        elif type(cnst) == cnf.less:
            return LT(terms, cnst.threshold)
    else:
        raise RuntimeError(
            "[Internal Error] Unknown type of constraints found: {}".format(type(cnst)))


def toCNFgen(cnf, f):
    v = ToCNFgenVisitor(cnf)
    v.visit(f)


class ToCNFgenVisitor(Visitor):
    def __init__(self, cnfgenInstance):
        self.cnf = cnfgenInstance

    def genericVisit(self, x):
        self.visit(transformToCNF(x))

    def visit_And(self, conjunction):
        for x in conjunction:
            self.visit(x)

    def visit_Or(self, disjunction):
        self.cnf.add_clause(list(map(lit2CNFgenLit, disjunction)))

    def visit_Inequality(self, ineq):
        def toArgs(listOfTuples, operator, rhs):
            return list(sum(listOfTuples, ())) + [operator, rhs]

        ineq = ineq.normalizedVariables()
        self.cnf.add_linear(*toArgs(ineq.terms, ">=", ineq.rhs))


class VarToInt(dict):
    def __init__(self):
        self.varCount = 1

    def __getitem__(self, var):
        value = self.setdefault(var, self.varCount)
        if value == self.varCount:
            self.varCount += 1
        return value


def toOPB(f, file=sys.stdout):
    v = ToOPBVisitor(file)
    v.visit(f)
    v.printHeader()
    v.visit(f)


class ToOPBVisitor(Visitor):
    def __init__(self, file):
        self.file = file
        self.vars = VarToInt()
        self.print = False
        self.constraintCount = 0

    def printHeader(self):
        self.print = True
        print("* #variable= %i #constraint= %i" %
              (self.vars.varCount - 1, self.constraintCount))
        for var, value in self.vars.items():
            print("* %s = x%i" % (str(var), value))

    def genericVisit(self, x):
        self.visit(transformToCNF(x))

    def visit_And(self, conjunction):
        for x in conjunction:
            self.visit(x)

    def visit_Or(self, disjunction):
        self.visit(GEQ([(1, x) for x in disjunction], 1))

    def visit_Inequality(self, ineq):
        self.constraintCount += 1

        ineq = ineq.normalizedVariables()
        if self.print:
            print(" ".join(["%+i x%i" % (a, self.vars[x]) for a, x in ineq.terms]),
                  end='', file=self.file)
            print(" >= %i;" % (ineq.rhs), file=self.file)
        else:
            # touch variables, so they are recorded
            for _, x in ineq.terms:
                self.vars[x]
