from virtual import VirtualInvolution, VirtualPermutation
from collections import defaultdict


REDUCED_WORDS_CACHE = {}
INVOLUTION_WORDS_CACHE = {}


class AffinePermutation:

    """
    Simple class implementing affine permutations.
    """

    def __init__(self, *oneline):
        if len(oneline) == 1 and type(oneline[0]) != int:
            oneline = [i for i in oneline[0]]

        n = len(oneline)
        assert n >= 2
        assert list(sorted(i % n for i in oneline)) == list(range(n))

        offset = (sum(oneline) - (n - 1) * n // 2) // n
        self.oneline = n * [0]
        for i in range(n):
            q = (i - offset) // n
            r = (i - offset) % n
            self.oneline[i] = oneline[r] + q * n
        self.oneline = tuple(self.oneline)

        self.rank = n
        self._cycle_set = None
        self._right_descent_set = None
        self._left_descent_set = None
        self._code = None

    @classmethod
    def identity(cls, rank):
        oneline = list(range(rank))
        return AffinePermutation(oneline)

    @classmethod
    def simple_transposition(cls, i, rank):
        return AffinePermutation.transposition(i, i + 1, rank)

    @classmethod
    def transposition(cls, i, j, rank):
        if j > i:
            i, j = j, i
        assert (j - i) % rank != 0
        oneline = list(range(i, i + rank))
        oneline[0] = j
        oneline[(j - i) % rank] = i - ((j - i) // rank) * rank
        return AffinePermutation(oneline)

    def star(self):
        return AffinePermutation(reversed([self.rank + 1 - i for i in self.oneline]))

    def __call__(self, i):
        q = i // self.rank
        r = i % self.rank
        return self.oneline[r] + q * self.rank

    def inverse(self):
        oneline_map = {}
        for i in range(self.rank):
            x = self(i)
            q = x // self.rank
            r = x % self.rank
            oneline_map[r] = i - q * self.rank
        assert set(oneline_map.keys()) == set(range(self.rank))
        oneline = [oneline_map[i] for i in range(self.rank)]
        return AffinePermutation(*oneline)

    def __mul__(self, other):
        assert self.rank == other.rank
        assert type(other) == AffinePermutation
        newline = [self(other(i)) for i in range(self.rank)]
        return AffinePermutation(*newline)

    def __pow__(self, e):
        assert type(e) == int
        if e < 0:
            return self.inverse()**(-e)
        elif e == 0:
            return AffinePermutation(range(self.rank))
        elif e % 2 == 1:
            return self * self**(e - 1)
        else:
            w = self**(e // 2)
            return w * w

    def __mod__(self, other):
        # the magic function % implements the Demazure product for affine permuations
        assert type(other) == AffinePermutation
        assert other.rank == self.rank
        ans = self
        for i in other.get_reduced_word():
            if i not in ans.right_descent_set:
                ans *= AffinePermutation.simple_transposition(i, self.rank)
        return ans

    def __lt__(self, other):
        """Determines lexicographic order on one-line representation."""
        assert type(other) == AffinePermutation
        assert self.rank == other.rank
        for i in range(1, self.rank + 1):
            if self(i) > other(i):
                return False
            if self(i) < other(i):
                return True
        return False

    def __eq__(self, other):
        assert type(other) == AffinePermutation
        assert self.rank == other.rank
        return self.oneline == other.oneline

    def __ne__(self, other):
        return not (self == other)

    def __repr__(self):
        n = self.rank
        s = [
            '...',
            ', '.join(map(str, [self(-n + i + 1) for i in range(n)])),
            ', '.join(map(str, [self(i + 1) for i in range(n)])),
            ', '.join(map(str, [self(n + i + 1) for i in range(n)])),
            '...'
        ]
        return '[ ' + ' | '.join(s) + ' ]'

    def __hash__(self):
        return hash(self.oneline)

    @property
    def code(self):
        if self._code is None:
            code = []
            for i in range(1, 1 + self.rank):
                c = 0
                for j in range(i + 1, self.rank + i):
                    if self(j) < self(i):
                        c += (self(i) - self(j)) // self.rank + 1
                code += [c]
            self._code = tuple(code)
        return self._code

    def __len__(self):
        return sum(self.code)

    @classmethod
    def from_code(cls, code):
        assert all(i >= 0 for i in code) and not all(i > 0 for i in code)
        n = len(code)
        indices = [i for i in range(n) if code[i] != 0 and code[(i + 1) % n] == 0]
        if indices:
            i = indices[0]
            newcode = list(code)
            newcode[(i + 1) % n], newcode[i] = newcode[i] - 1, 0
            return cls.from_code(newcode) * AffinePermutation.simple_transposition(i + 1, n)
        return AffinePermutation.identity(n)

    @classmethod
    def all(cls, n, length_bound=None, finite=False):
        def increment_fn(w, i):
            return w * cls.simple_transposition(i, n)

        for w in cls._generate(n, cls.identity(n), increment_fn, length_bound, finite):
            yield w

    @classmethod
    def involutions(cls, n, involution_length_bound=None, finite=False):
        def increment_fn(w, i):
            return cls.simple_transposition(i, n) % w % cls.simple_transposition(i, n)

        for w in cls._generate(n, cls.identity(n), increment_fn, involution_length_bound, finite):
            yield w

    @classmethod
    def _generate(cls, n, start, increment_fn, length_bound, finite):
        level, next_level, length = {start}, set(), 0
        while level:
            for w in level:
                if length_bound is None or length < length_bound:
                    next_level |= {increment_fn(w, i) for i in w.right_ascent_set if not (finite and i == n)}
                yield w
            level, next_level, length = next_level, set(), length + 1

    @property
    def length(self):
        return len(self)

    @property
    def absolute_length(self):
        return self.rank - len(self.cycle_set)

    @property
    def involution_length(self):
        if self.is_involution():
            return (self.length + self.absolute_length) // 2

    def is_involution(self):
        return all(self(self(i)) == i for i in range(self.rank))

    def is_identity(self):
        return len(self) == 0

    @property
    def cycle_set(self):
        if self._cycle_set is None:
            self._cycle_set = set()
            remaining = set(range(self.rank))
            while len(remaining) > 0:
                i = min(remaining)
                remaining.remove(i)
                cycle = [i]
                while True:
                    j = self(cycle[-1])
                    if cycle[0] == j:
                        break
                    remaining.remove(j % self.rank)
                    cycle.append(j)
                self._cycle_set.add(tuple(cycle))
        return self._cycle_set

    @property
    def right_descent_set(self):
        if self._right_descent_set is None:
            self._right_descent_set = set()
            for i in range(1, self.rank + 1):
                if(self(i) > self(i + 1)):
                    self._right_descent_set.add(i)
        return self._right_descent_set

    @property
    def left_descent_set(self):
        if self._left_descent_set is None:
            self._left_descent_set = self.inverse().right_descent_set
        return self._left_descent_set

    @property
    def right_ascent_set(self):
        return set(range(1, self.rank + 1)) - self.right_descent_set

    @property
    def left_ascent_set(self):
        return set(range(1, self.rank + 1)) - self.left_descent_set

    def is_right_descent(self, i):
        return i in self.right_descent_set

    def is_left_descent(self, i):
        return i in self.left_descent_set

    def get_right_descent(self):
        return min(self.right_descent_set) if self.right_descent_set else None

    def get_left_descent(self):
        return min(self.left_descent_set) if self.left_descent_set else None

    def get_reduced_word(self):
        i = self.get_right_descent()
        if i is None:
            return ()
        w = self * AffinePermutation.simple_transposition(i, self.rank)
        return w.get_reduced_word() + (i,)

    @property
    def reduced_words(self):
        if self.oneline not in REDUCED_WORDS_CACHE:
            if self.is_identity():
                words = {()}
            else:
                words = set()
                for i in self.right_descent_set:
                    s = AffinePermutation.simple_transposition(i, self.rank)
                    words |= {e + (i,) for e in (self * s).reduced_words}
            REDUCED_WORDS_CACHE[self.oneline] = words
        return REDUCED_WORDS_CACHE[self.oneline]

    def get_involution_word(self):
        return self.get_min_atom().get_reduced_word()

    @property
    def involution_words(self):
        if self.is_involution():
            oneline = tuple(self.oneline)
            if oneline not in INVOLUTION_WORDS_CACHE:
                INVOLUTION_WORDS_CACHE[oneline] = set()
                for w in self.get_atoms():
                    INVOLUTION_WORDS_CACHE[oneline] |= w.reduced_words
            return INVOLUTION_WORDS_CACHE[oneline]

    def is_finite_type(self):
        return all(1 <= self(i + 1) <= self.rank for i in range(self.rank))

    def is_atom(self):
        z = self.inverse() % self
        return z.involution_length == self.length

    def get_min_atom(self):
        assert self.is_involution()
        oneline = []
        for i in range(1, self.rank + 1):
            if i < self(i):
                oneline += [self(i), i]
            elif i == self(i):
                oneline += [i]
        return AffinePermutation(oneline).inverse()

    def get_max_atom(self):
        assert self.is_involution()
        oneline = []
        for j in range(1, self.rank + 1):
            if self(j) < j:
                oneline += [j, self(j)]
            elif j == self(j):
                oneline += [j]
        return AffinePermutation(oneline).inverse()

    def get_atoms(self):
        assert self.is_involution()
        level = {self.get_min_atom().inverse()}
        while level:
            next_level = set()
            for w in level:
                yield w.inverse()
                for i in range(1, self.rank + 1):
                    c, a, b = w(i), w(i + 1), w(i + 2)
                    if a < b < c:
                        s = AffinePermutation.simple_transposition(i, self.rank)
                        t = AffinePermutation.simple_transposition(i + 1, self.rank)
                        next_level.add(w * t * s)
            level = next_level

    def virtualize(self, i, j, invol):
        assert type(i) == type(j) == int and type(invol)== AffinePermutation
        assert i < j
        assert i % invol.rank != j % invol.rank
        assert invol(i) == j or invol(i) % invol.rank != j % invol.rank
        assert self.rank == invol.rank
        assert invol.is_involution()

        w, n = self.inverse(), self.rank
        inputs = sorted({self(i), self(j), self(invol(i)), self(invol(j))})
        outputs = [w(x) for x in inputs]
        inputs_index = {v: i + 1 for i, v in enumerate(inputs)}
        outputs_index = {v: i + 1 for i, v in enumerate(sorted(outputs))}

        mirror_extensions = defaultdict(set)
        double_extensions = defaultdict(set)
        single_extensions = defaultdict(set)

        lower = min(min(inputs) - max(inputs), min(outputs) - max(outputs)) // n - 1
        upper = max(max(inputs) - max(outputs), max(outputs) - min(outputs)) // n + 2
        for k in range(lower, upper):
            shifted = [x + k * n for x in inputs]

            if set(inputs) & set(shifted):
                continue

            new_inputs = sorted(inputs + shifted)
            new_outputs = [w(x) for x in new_inputs]
            base = tuple(inputs_index[x] if x in inputs else -inputs_index[x - k * n] for x in new_inputs)
            pi = tuple(outputs_index[x] if x in outputs else -outputs_index[x - k * n] for x in new_outputs)
            mirror_extensions[base].add(pi)

        lower = min(inputs)
        while any(invol(x) > min(inputs) or max(w(x), w(invol(x))) > min(outputs) for x in range(lower, lower + n)):
            lower -= n

        upper = max(inputs) + 1
        while any(invol(x) < max(inputs) or min(w(x), w(invol(x))) < max(outputs)for x in range(upper - n, upper)):
            upper += n

        for x in range(lower, upper):
            if x % n in {z % n for z in inputs}:
                continue

            if w(x) == invol(w(x)):
                new_outputs = [w(z) for z in sorted(inputs + [x])]

                def format_output(z):
                    ch = VirtualPermutation.FIXED_CHAR
                    return outputs_index[z] if z in outputs else ch

                base = tuple(map(format_output, sorted(new_outputs)))
                pi = tuple(map(format_output, new_outputs))
                single_extensions[base].add(pi)

            if w(x) < invol(w(x)):
                y = self(invol(w(x)))
                new_outputs = [w(z) for z in sorted(inputs + [x, y])]

                def format_output(z):
                    ch1, ch2 = VirtualPermutation.CYCLE_CHARS
                    return outputs_index[z] if z in outputs else (ch1 if z == w(x) else ch2)

                base = tuple(map(format_output, sorted(new_outputs)))
                pi = tuple(map(format_output, new_outputs))
                double_extensions[base].add(pi)

        order = tuple(outputs_index[x] for x in outputs)
        return VirtualPermutation(order, mirror_extensions, double_extensions, single_extensions)
