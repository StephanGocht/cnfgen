#!/usr/bin/env python
# -*- coding:utf-8 -*-


from ..cnf import CNF, weighted_eq, weighted_geq

from ..cmdline import register_cnf_transformation_subcommand
from ..transformations import register_cnf_transformation

###
# Substitions
###


@register_cnf_transformation
class Linearization(CNF):
    """Apply a substitution to a formula
    """

    def __init__(self, cnf, arity, num, den, no_rat, equality, divide):
        """Build a new CNF linearizing clauses

        Arguments:
        - `cnf`: the original cnf
        """
        self._orig_cnf = cnf
        super(Linearization, self).__init__([], header=cnf._header)

        self._header = "Linearized formula with arity {}\n\n".format(arity) \
            + self._header

        varname = [None]+list(self._orig_cnf.variables())

        def newvarname(l, i):
            return "{{{}}}^{}".format(varname[l], i)

        def newvar(l, i):
            return (l-1)*arity+i+1

        for l in range(1, len(varname)):
            for j in range(arity):
                self.add_variable(newvarname(l, j))

        # build and add new clauses
        for orig_cnst in self._orig_cnf._constraints:
            for orig_cls in orig_cnst.clauses():
                positive_literals = [x for x in orig_cls if x > 0]
                negative_literals = [-x for x in orig_cls if x < 0]
                p = len(positive_literals)
                n = len(negative_literals)
                pweight = 0
                nweight = 0
                if (p == 0):
                    if (n > 1):
                        raise NotImplemented()
                    nweight = -den
                    threshold = -num + (1 if no_rat else 0)
                    if (divide):
                        nweight /= den
                        threshold = -(-threshold//den)
                elif (n == 0):
                    if (p > 1):
                        raise NotImplemented()
                    pweight = den
                    threshold = num
                    if (divide):
                        pweight /= den
                        threshold = -(-threshold//den)
                else:
                    pweight = n
                    nweight = -p
                    threshold = 0
                q = []
                if pweight:
                    q.extend([(pweight, newvar(l, j))
                              for l in positive_literals for j in range(arity)])
                if nweight:
                    q.extend([(nweight, newvar(l, j))
                              for l in negative_literals for j in range(arity)])
                if equality:
                    self._constraints.append(weighted_eq(*q, value=threshold))
                else:
                    self._constraints.append(
                        weighted_geq(*q, threshold=threshold))

        self._length = None
#        assert self._check_coherence()


@register_cnf_transformation_subcommand
class LinearizationCmd:
    name = 'lin'
    description = 'linearize clauses with arity N'

    @staticmethod
    def setup_command_line(parser):
        parser.add_argument('A', type=int, nargs='?', default=3,
                            action='store', help="arity (default: 3)")
        parser.add_argument('N', type=int, nargs='?',
                            action='store', help="RHS coefficient (default: A)")
        parser.add_argument('D', type=int, nargs='?', default=2,
                            action='store', help="LHS coefficients (default:2)")
        parser.add_argument('--no-rat', action='store_true',
                            help="subtract 1 from the RHS on negative clauses")
        parser.add_argument('--equality', action='store_true',
                            help="replace inequalities by equalities")
        parser.add_argument('--divide', action='store_true',
                            help="divide by the RHS with rounding")

    @staticmethod
    def transform_cnf(F, args):
        if args.N is None:
            args.N = args.A
        return Linearization(F, args.A, args.N, args.D, args.no_rat, args.equality, args.divide)
