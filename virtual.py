import itertools


class VirtualInvolution(object):

    """
    Simple class implementing involutions of {1, 2, ..., m} and related methods
    for use in checking covering and toggling properties.
    """

    def __init__(self, *weak_cycles):
        """For involution y, weak_cycles should be list of all pairs (a, b) with a <= b == y(b)."""
        self.involution = {}
        for a, b in weak_cycles:
            self.involution[a], self.involution[b] = b, a
        assert {x for x in self.involution} == {x + 1 for x in range(self.rank)}
        self.fixed = {x for x in self.involution if self.involution[x] == x}
        self.cycles = {(x, y) for x, y in self.involution.items() if x < y}

    @classmethod
    def from_permutation(cls, y, i, j):
        assert y(y(i)) == i and y(y(j)) == j
        inputs = sorted({i, j, y(i), y(j)})
        index = {v: i + 1 for i, v in enumerate(inputs)}
        weak_cycles = [(index[x], index[y(x)]) for x in inputs]
        return VirtualInvolution(*weak_cycles), index[i], index[j]

    @property
    def rank(self):
        return len(self.involution)

    def __call__(self, x):
        return self.involution[x]

    def __hash__(self):
        return hash(tuple(sorted(self.involution.items())))

    def __eq__(self, other):
        assert type(other) == VirtualInvolution
        return self.involution == other.involution

    def __repr__(self):
        def format_cycle(x):
            characters = map(str, x)
            return '(' + ' '.join(characters) + ')'

        return ''.join(map(format_cycle, sorted(self.cycles | {(c,) for c in self.fixed})))

    def tau(self, i, j):
        """Returns involution given by tau_ij(self)."""
        a, b = self(i), self(j)

        if i <= a < b <= j:
            cycles = [(i, j)]
        elif a == i < j < b or i < a < j < b:
            cycles = [(i, b)]
        elif a < i < j == b or a < i < b < j:
            cycles = [(a, j)]
        elif a < i < j < b or i < j < a < b or a < b < i < j:
            cycles = [(i, b), (j, a)]
        elif i < b < a < j:
            cycles = [(i, j), (a, b)]
        else:
            return self

        cycles += [(x, y) for x, y in self.involution.items() if not ({x, y} & {i, j})]
        cycles += [(x, x) for x in range(1, 1 + self.rank) if not any(x in c for c in cycles)]
        return VirtualInvolution(*cycles)

    def toggle(self, virtual_atom, i, j):
        """
        Given virtual atom and integers i < j, returns pair k < l
        defined in Toggling property theorem of corresponding paper.
        """
        w = virtual_atom

        a, b, c = i, j, self(i)
        if j == self(j) and a < b < c and w(c) < w(a) < w(b):
            return (b, c)

        a, b, c = self(j), i, j
        if i == self(i) and a < b < c and w(b) < w(c) < w(a):
            return (a, b)

        a, b, c, d = i, j, self(j), self(i)
        if a < b < c < d and w(d) < w(a) < w(c) < w(b):
            return (c, d)

        if a < b < c < d and w(c) < w(d) < w(a) < w(b):
            return (b, d)

        a, b, c, d = self(j), self(i), i, j
        if a < b < c < d and w(c) < w(b) < w(d) < w(a):
            return (a, b)

        if a < b < c < d and w(c) < w(d) < w(a) < w(b):
            return (a, c)

        a, b, c, d = i, self(j), j, self(i)
        if a < b < c < d and w(d) < w(a) < w(c) < w(b):
            return (c, d)

        a, b, c, d = self(j), i, self(i), j
        if a < b < c < d and w(c) < w(b) < w(d) < w(a):
            return (a, b)

        raise NotImplementedError

    REASON_F1 = 'F1: y has fixed points a < b but pi(b) < pi(a)'
    REASON_F2 = 'F2: y has fixed point a and cycle (b, c) with b < a < c but pi(c) < pi(a) < pi(b)'
    REASON_F3 = 'F3: y has fixed point a and cycle (b, c) with a < b < c but pi(c) < pi(a)'
    REASON_F4 = 'F4: y has fixed point a and cycle (b, c) with b < c < a but pi(a) < pi(b)'
    REASON_C1 = 'C1: y has cycle (a, b) with a < b but pi(a) < pi(b)'
    REASON_C2 = 'C2: y has cycles (a, b) and (c, d) with a < c and b < d but pi(d) < pi(a)'
    REASON_C3 = 'C3: y has cycles (a, b) and (c, d) with a < c < d < b but pi(b) < pi(c) < pi(a)'
    REASON_C4 = 'C4: y has cycles (a, b) and (c, d) with a < c < d < b but pi(b) < pi(d) < pi(a)'
    REASON_B1 = 'B1: exists integer e with i < e < j and pi(i) < pi(e) < pi(j)'
    REASON_B2 = 'B2: exists integer e with i - mn < e < j - mn and pi(i - mn) < pi(e) < pi(j - mn)'

    def _invalid_configurations_generator(self, virtual_permutation, required_ascents):
        """
        Yields all tuples (base, pi, reason, witness) that detect failure of conditions
        needed for virtual_permutation to be virtual atom of self and for all required_ascents
        to be contained in Cov(virtual_permutation). All reasons are class defined constants.
        All witnesses are tuples (a, b, a', b') where a <= b = self(a) and a' <= b' = self(a').
        """
        for base, permutations in virtual_permutation.extensions.items():
            for pi in permutations:
                for i, j in required_ascents:
                    if not self._has_bruhat_covering_ascent(i, j, base, pi):
                        yield base, pi, self.REASON_B1, None

                    if -i in base and not self._has_bruhat_covering_ascent(-i, -j, base, pi):
                        yield base, pi, self.REASON_B2, None

                for a, pi_a in self._normalized_fixed_points(base, pi):
                    for b, pi_b in self._normalized_fixed_points(base, pi):
                        if a < b and pi_b < pi_a:
                            yield base, pi, self.REASON_F1, (a, a, b, b)

                    for b, pi_b, c, pi_c in self._normalized_cycles(base, pi):
                        if b < a < c and pi_c < pi_a < pi_b:
                            yield base, pi, self.REASON_F2, (b, c, a, a)

                        if a < b and pi_c < pi_a:
                            yield base, pi, self.REASON_F3, (a, a, b, c)

                        if c < a and pi_a < pi_b:
                            yield base, pi, self.REASON_F4, (b, c, a, a)

                for a, pi_a, b, pi_b in self._normalized_cycles(base, pi):
                    if pi_a < pi_b:
                        yield base, pi, self.REASON_C1, (a, b)

                    for c, pi_c, d, pi_d in self._normalized_cycles(base, pi):
                        if a < c and b < d and pi_d < pi_a:
                            yield base, pi, self.REASON_C2, (a, b, c, d)

                        if a < c < d < b and pi_b < pi_c < pi_a:
                            yield base, pi, self.REASON_C3, (a, b, c, d)

                        if a < c < d < b and pi_b < pi_d < pi_a:
                            yield base, pi, self.REASON_C4, (a, b, c, d)

    def _normalized_fixed_points(self, base, pi):
        """
        For each fixed point of this involution, yields the pair (a, i)
        where a is the position of the fixed point in the linear order `base`
        and i is the position of the fixed point in the linear order `pi`.
        """
        base_index = {v: i for i, v in enumerate(base)}
        fixed = self.fixed | {-i for i in self.fixed} | {VirtualPermutation.FIXED_CHAR}
        for i, v in enumerate(pi):
            if v in fixed:
                a = base_index[v]
                yield (a, i)

    def _normalized_cycles(self, base, pi):
        """
        For each cycle (p < q) of this involution, yields the tuple (a, i, b, j)
        where a, b are the positions of p, q in the linear order `base`
        and i, j are the positions of p, q in the linear order `pi`.
        """
        base_index = {v: i for i, v in enumerate(base)}
        cycles = self.cycles | {(-i, -j) for i, j in self.cycles} | {VirtualPermutation.CYCLE_CHARS}
        for i, v in enumerate(pi):
            for j, w in enumerate(pi):
                if (v, w) in cycles:
                    a, b = base_index[v], base_index[w]
                    assert a < b
                    yield (a, i, b, j)

    @classmethod
    def _has_bruhat_covering_ascent(cls, i, j, base, pi):
        """
        Returns True if exists e such that i < e < j in order defined by base
        and the tuple pi has the form pi = (..., i, ..., e, ..., j, ...).
        """
        base_index = {a: index for index, a in enumerate(base)}
        pi_index = {a: index for index, a in enumerate(pi)}

        if pi_index[i] > pi_index[j]:
            return False

        base_interval = {base[e] for e in range(base_index[i] + 1, base_index[j])}
        pi_interval = {pi[e] for e in range(pi_index[i] + 1, pi_index[j])}
        return len(base_interval & pi_interval) == 0

    def get_invalid_configurations(self, virtual, required_ascents=tuple()):
        """Returns dict mapping base orders to dicts mapping permutation to (reason, witness)
        pairs that detect failure of input virtual to be virtual atom of self and for all
        required_ascents to be contained in Cov(virtual_permutation).
        """
        invalid_dictionary = {}
        for base, pi, reason, witness in self._invalid_configurations_generator(virtual, required_ascents):
            if base not in invalid_dictionary:
                invalid_dictionary[base] = {}
            if pi not in invalid_dictionary[base]:
                invalid_dictionary[base][pi] = []
            if witness is not None:
                witness = tuple(base[i] for i in witness)
            invalid_dictionary[base][pi] += [(reason, witness)]
            invalid_dictionary[base][pi].sort(key=lambda x: x[0])
        return invalid_dictionary

    def is_virtual_atom(self, virtual_permutation, required_ascents=tuple()):
        assert type(virtual_permutation) == VirtualPermutation
        assert self.rank == virtual_permutation.rank
        return len(self.get_invalid_configurations(virtual_permutation, required_ascents)) == 0

    def get_virtual_atoms(self, required_ascents=tuple()):
        """
        Generates all VirtualPermutations w that are virtual atoms of self and
        such that (i, j) is in Cov(w) for each (i, j) in list of required_ascents.
        """
        for pi in itertools.permutations(range(1, self.rank + 1)):
            virtual = VirtualPermutation(pi, {}, {}, {})
            if self.is_virtual_atom(virtual, required_ascents):
                all_mirror, all_double, all_single = VirtualPermutation.maximal_extensions(pi)
                virtual = VirtualPermutation(pi, all_mirror, all_double, all_single)
                invalid_dictionary = self.get_invalid_configurations(virtual, required_ascents)
                mirror = {e: all_mirror[e] - set(invalid_dictionary[e].keys()) for e in all_mirror}
                double = {e: all_double[e] - set(invalid_dictionary[e].keys()) for e in all_double}
                single = {e: all_single[e] - set(invalid_dictionary[e].keys()) for e in all_single}
                yield VirtualPermutation(pi, mirror, double, single)

    @classmethod
    def all(cls, maximum_size=4, mimimal_type=True):
        """
        Generates all involutions of {1, 2, ..., m} for 2 <= m <= maximum_size. If
        minimal_type is set to True, only yields involutions with at most two cycles.
        """
        for n in range(2, maximum_size + 1):
            for pi in itertools.permutations(range(n)):
                if all(pi[pi[i]] == i for i in range(n)):
                    weak_cycles = [(i + 1, pi[i] + 1) for i in range(n) if i <= pi[i]]
                    if len(weak_cycles) <= 2 or not mimimal_type:
                        yield VirtualInvolution(*weak_cycles)


class VirtualPermutation(object):

    """
    Class implementing VirtualPermutation objects as defined in Section 5.2 of corresponding paper.
    """

    CYCLE_CHARS = ('P', 'Q')
    FIXED_CHAR = 'R'

    def __init__(self, permutation, mirror_extensions, double_extensions, single_extensions):
        self.permutation = tuple(permutation)
        assert sorted(self.permutation) == [x + 1 for x in range(self.rank)]
        self.base = tuple(sorted(permutation))
        self.mirror_extensions = {
            e: set(mirror_extensions.get(e, set()))
            for e in self.mirror(self.base)
        }
        self.double_extensions = {
            e: set(double_extensions.get(e, set()))
            for e in self.shuffle(self.base, self.CYCLE_CHARS)
        }
        self.single_extensions = {
            e: set(single_extensions.get(e, set()))
            for e in self.shuffle(self.base, [self.FIXED_CHAR])
        }

    @property
    def rank(self):
        return len(self.permutation)

    @property
    def extensions(self):
        ans = {self.base: {self.permutation}}
        for k, v in self.mirror_extensions.items():
            ans[k] = v
        for k, v in self.double_extensions.items():
            ans[k] = v
        for k, v in self.single_extensions.items():
            ans[k] = v
        return ans

    def __call__(self, x):
        """Returns 1-based index i such that self.permutation(i) == x."""
        for i, v in enumerate(self.permutation):
            if v == x:
                return i + 1

    def contains(self, other):
        """
        Returns True if self and other have same permutation field, and the image
        of each order under the extension maps of self is a subset of the image of
        the same under the corresponding maps of other.
        """
        assert type(other) == VirtualPermutation
        if self.permutation != other.permutation:
            return False
        return all(other.extensions.get(k, set()).issubset(v) for k, v in self.extensions.items())

    def transpose(self, i, j):
        """Returns VirtualPermutation permutation self * (i, j)."""
        assert i in self.base and j in self.base
        t = {i: j, j: i, -i: -j, -j: -i}

        def transform(tup):
            return tuple(t.get(x, x) for x in tup)

        permutation = transform(self.permutation)
        mirror = {k: set(map(transform, v)) for k, v in self.mirror_extensions.items()}
        double = {k: set(map(transform, v)) for k, v in self.double_extensions.items()}
        single = {k: set(map(transform, v)) for k, v in self.single_extensions.items()}
        return VirtualPermutation(permutation, mirror, double, single)

    @classmethod
    def shuffle(cls, tup_a, tup_b):
        """Given disjoint tuples as inputs, generates all of their shuffles."""
        m, n = len(tup_a), len(tup_b)
        for inds_a in itertools.combinations(range(m + n), m):
            inds_b = (i for i in range(m + n) if i not in inds_a)
            interlaced = (m + n) * [0]
            for i, x in enumerate(inds_a):
                interlaced[x] = tup_a[i]
            for i, x in enumerate(inds_b):
                interlaced[x] = tup_b[i]
            yield tuple(interlaced)

    @classmethod
    def mirror(cls, tup_a):
        """
        Given a tuple of positive integers tup_a = (i, j, k, ...) as input, generates all shuffles
        of tup_a and -tup_a = (-i, -j, -k, ... ) in which -a appears before a for each a > 0.
        """
        assert all(i > 0 for i in tup_a)
        for e in cls.shuffle(tup_a, [-i for i in tup_a]):
            firsts = set()
            for i in range(len(e)):
                if -e[i] not in firsts:
                    firsts.add(e[i])
            if max(firsts) < 0:
                yield e

    @classmethod
    def maximal_extensions(cls, pi):
        """
        Returns maps M, D, S such that VirtualPermutation(pi, M, D, S)
        contains every VirtualPermutation whose permutation field is pi.
        """
        base = tuple(range(1, len(pi) + 1))
        all_mirror = {
            e: set(cls.mirror(pi)) for e in cls.mirror(base)
        }
        all_double = {
            e: set(cls.shuffle(pi, tuple(reversed(cls.CYCLE_CHARS))))
            for e in cls.shuffle(base, cls.CYCLE_CHARS)
        }
        all_single = {
            e: set(cls.shuffle(pi, [cls.FIXED_CHAR]))
            for e in cls.shuffle(base, [cls.FIXED_CHAR])
        }
        return all_mirror, all_double, all_single

    def __repr__(self):
        def tostring(tup):
            if -1 in tup:
                return ' < '.join([('+' + str(i)) if i > 0 else str(i) for i in tup])
            return ' < '.join(map(str, tup))

        w_str = ''.join(map(str, self.permutation))
        lines = ['virtual permutation (w, M, D, S) where\n\n  w = %s\n' % w_str]

        mappings = [
            ('M', self.mirror_extensions),
            ('D', self.double_extensions),
            ('S', self.single_extensions)
        ]
        for label, mapping in mappings:
            for key, perms in mapping.items():
                if perms:
                    perms = sorted(map(tostring, perms))
                    lines += ['  %s( %s ) = { ' % (label, tostring(key))]
                    offset = len(lines[-1]) * ' '
                    lines[-1] += perms[0]
                    for pi in perms[1:]:
                        lines[-1] += ','
                        lines += [offset + pi]
                    lines[-1] += ' }'
                else:
                    lines += ['  %s( %s ) = { }' % (label, tostring(key))]
            if mapping:
                lines += ['']

        return '\n'.join(lines)


def check_covering_property():
    print()
    print('**************************')
    print('Checking covering property')
    print('**************************')
    cases = [
        (y, i, j, y.tau(i, j))
        for y in VirtualInvolution.all()
        for i, j in itertools.combinations(range(1, y.rank + 1), 2)
        if y != y.tau(i, j)
    ]
    print()
    print('Suppose y is an involution with at most two cycles.')
    print('Suppose i < j are such that y != z = tau_ij(y).')
    print()
    print('Then y, i, j, and z must belong to one of the following cases:')
    print()
    for y, i, j, z in cases:
        pad = (10 - len(str(y))) * ' '
        print('  y = %s,%s i = %s, j = %s, z = %s' % (y, pad, i, j, z))
    input('\n(press enter to continue)\n')
    case = 0
    total = len(cases)
    for y, i, j, z in cases:
        atoms = list(y.get_virtual_atoms(required_ascents={(i, j)}))
        assert len(atoms) == 1
        w = atoms.pop()
        wt = w.transpose(i, j)
        check = z.is_virtual_atom(wt)
        assert check
        case += 1
        print()
        print('Case %s of %s:' % (case, total))
        print()
        print('Suppose')
        print()
        print('  y = %s' % y)
        print('  i = %s' % i)
        print('  j = %s' % j)
        print('  z = %s = tau_{ij}(y).' % z)
        print()
        print('The unique maximal virtual atom Pi of y with (i, j) in Cov(Pi)')
        print('is the %s' % w)
        print('Pi * (i, j) is the %s' % wt)
        print('Pi * (i, j) is a virtual atom of z = %s: %s' % (z, check))
        print()
        input('(press enter to continue)\n')
    print()
    print('**********')
    print('Conclusion')
    print('**********')
    print()
    print('In all cases, Pi * (i, j) is a virtual atom of z = tau_ij(y).')
    print()
    print('Hence if y is an involution with at most two cycles and y != tau_ij(y),')
    print('and Pi is a virtual atom of y with (i, j) in Cov(Pi), then Pi * (i, j)')
    print('is a virtual atom of tau_ij(y).')
    print()


def check_toggling_property():
    print()
    print('**************************')
    print('Checking toggling property')
    print('**************************')
    cases = [
        (y, i, j, w)
        for y in VirtualInvolution.all()
        for i, j in itertools.combinations(range(1, y.rank + 1), 2)
        for w in y.get_virtual_atoms(required_ascents={(i, j)})
        if y == y.tau(i, j)
    ]
    print()
    print('Suppose y is an involution with at most two cycles.')
    print('Suppose i < j are such that y == tau_ij(y).')
    print('Suppose Pi = (w, M, D, S) is a virtual atom of y with (i, j) in Cov(Pi).')
    print()
    print('Then y, i, j, and w must belong to one of the following cases:')
    print()
    for y, i, j, w in cases:
        pad = (10 - len(str(y))) * ' '
        w_str = ''.join(map(str, w.permutation))
        print('  y = %s,%s i = %s, j = %s, w = %s' % (y, pad, i, j, w_str))
    input('\n(press enter to continue)\n')
    case = 0
    total = len(cases)
    for y, i, j, w in cases:
        k, l = y.toggle(w, i, j)
        v = w.transpose(i, j).transpose(k, l)
        check = y.is_virtual_atom(v)
        assert check
        case += 1
        print()
        print('Case %s of %s:' % (case, total))
        print()
        print('Suppose')
        print()
        print('  y = %s' % y)
        print('  i = %s' % i)
        print('  j = %s' % j)
        print()
        print('and Pi is the maximal virtual atom of y with (i, j) in Cov(Pi)')
        print('given by the %s' % w)
        print('Then k = %s and l = %s, and Pi * (i, j)(k, l) is the %s' % (k, l, v))
        print('Pi * (i, j)(k, l) is a virtual atom of y = %s: %s' % (y, check))
        print()
        input('(press enter to continue)\n')
    assert case == total
    print()
    print('**********')
    print('Conclusion')
    print('**********')
    print()
    print('In all cases, Pi * (i, j)(k, l) is a virtual atom of y.')
    print()
    print('Hence if y is an involution with at most two cycles and y == tau_ij(y),')
    print('and Pi is a virtual atom of y with (i, j) in Cov(Pi), then the virtual')
    print('permutation Pi * (i, j)(k, l) is another virtual atom of y.')
    print()


def check_properties():
    print()
    print('Virtual atoms calculator')
    print('========================')
    while True:
        print('Enter 1 to check covering property.')
        print('Enter 2 to check toggling property.')
        print('Enter 3 to quit.')
        choice = input('\nInput: ')
        if choice == '1':
            check_covering_property()
            break
        if choice == '2':
            check_toggling_property()
            break
        if choice == '3':
            break
        print()


if __name__ == '__main__':
    check_properties()
