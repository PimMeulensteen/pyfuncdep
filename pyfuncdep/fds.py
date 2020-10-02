""" This file contains classes and functionality to solve certain aspects
of a sysmtem of functional dependencies (FDs). """
from __future__ import annotations
from functools import reduce
from itertools import chain, combinations
from typing import List, Any, Iterable, Set, FrozenSet, Union


def _powerset(iterable: Iterable) -> Iterable:
    """ Give the powerset of a iterable. """
    iterable_list = list(iterable)
    return map(
        frozenset,
        chain.from_iterable(
            combinations(iterable_list, r) for r in range(len(iterable_list) + 1)
        ),
    )


class FD:
    """This is a class for a functional dependent relationship.
    This means: left -> right."""

    left: FrozenSet[Any]
    right: FrozenSet[Any]

    def __init__(self, a=None, b=None) -> None:
        if not a and not b:
            self.left = frozenset()
            self.right = frozenset()
            return
        elif b:
            self.left = frozenset(a)
            self.right = frozenset(b)
        else:
            self.left = frozenset(a[0])
            self.right = frozenset(a[-1])

    def is_trivial(self) -> bool:
        """ Return True if func_dep is trivial. We call a FD X->Y trivial
            if Y is a subset of X. """
        return self.right <= self.left

    def split_right(self) -> List[FD]:
        """ Split multiple values on the right into multi single-valued FDs """
        return [FD(self.left, r) for r in self.right]

    def __repr__(self) -> str:
        return str(self)

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, FD):
            return NotImplemented

        return self.left == other.left and self.right == other.right

    def __str__(self) -> str:
        return f"{','.join(sorted(self.left))} -> {','.join(sorted(self.right))}"

    def __hash__(self) -> int:
        return hash((self.left, self.right))


class FDs:
    """ This is a class for a system of FDs. """

    fds: Set[Any]
    alphabet: FrozenSet[Any]

    def __init__(self, fds: list = []) -> None:
        self.fds = set(fds)
        self.alphabet = self.find_alphabet()

    def find_alphabet(self) -> FrozenSet[Any]:
        """ Find the alphabet of a system of FDs """
        if not self.fds:
            return frozenset()
            
        result: Set[Any] = set()
        for i in self.fds:
            result.update(*i.left)
            result.update(*i.right)
        return frozenset(result)

    def append_fd(self, fd: FD) -> None:
        self.fds = self.fds.add(fd)
        self.alphabet = self.find_alphabet()


    def is_bcnf(self, func_dep_list: List[Set]) -> bool:
        """ Return True if the FDs are in BCNF, False otherwise """

        def condition_2(func_dep: FD, func_dep_list: List[Set]) -> bool:
            return any(
                i.issubset(func_dep.left) for i in func_dep_list
            )  # left contains a key of R.

        return all(fd.is_trivial() or condition_2(fd, func_dep_list) for fd in self.fds)

    def is_3nf(self, keys: Set[FrozenSet]) -> bool:
        """ Return True if the FDs are in 3NF, False otherwise """
        fds = self.split_right().fds

        def condition_2(func_dep: FD, keys: set) -> bool:
            # left contains a key of R.
            return any(i <= func_dep.left for i in keys)

        def condition_3(func_dep: FD, keys: set) -> bool:
            # B is a key attribute of R.
            return any(i >= func_dep.right for i in keys)

        return all(
            fd.is_trivial() or condition_2(fd, keys) or condition_3(fd, keys)
            for fd in fds
        )

    def split_right(self) -> FDs:
        """ Reutrn a new FDs object with A -> b where b is one attribute. """
        return FDs(sum([fd.split_right() for fd in self.fds], []))

    def is_minimal(self, my_test: FrozenSet[Any]) -> bool:
        """ Return True if the set is minimal, false otherwise. """
        if len(my_test) <= 1:
            return True
        return not any(i in self.cover_set(my_test - {i}) for i in my_test)

    def minimal_keys(self, g: FrozenSet[Any]) -> List[Any]:
        """ Find minimal keys for a given list g. """
        return [
            subset
            for subset in _powerset(g)
            if self.is_minimal(subset) and g <= self.cover_set(subset)
        ]

    def cover_set(self, my_test: FrozenSet[Any], fds: List[FD] = None) -> FrozenSet:
        """ Create the cover set for a given set. """
        if fds is None:
            fds = self.fds

        l = 0
        new_set = my_test.copy()
        while l < len(new_set):
            l = len(new_set)
            for fd in fds:
                if fd.left <= new_set:
                    new_set = new_set.union(fd.right)

        return new_set

    def determinants(self, B: FrozenSet[Any]) -> List[FrozenSet[Any]]:
        """ Return a list of determinants for the list of FD `B'. """
        list_of_a: List[FrozenSet[Any]] = []
        for pos in _powerset(self.alphabet):
            if not pos:
                continue
            if not B <= self.cover_set(pos):
                continue

            if not self.is_minimal(pos):
                continue

            if B <= pos:
                continue

            list_of_a.append(pos)

        return list_of_a

    def canonical(self) -> Set[FD]:
        """ Return a canonical for the current FD object. """

        def is_implied(F: List[FD], func_dep: FD) -> bool:
            """ Test if func_dep is implied by F-func_dep. """
            f_minus_fd = FDs([i for i in F if i != func_dep])
            if func_dep.right.issubset(f_minus_fd.cover_set(func_dep.left)):
                return True
            return False

        def reduce_left_side(self, func_dep: FD) -> FD:
            for y in func_dep.left:
                x_without_y = frozenset([i for i in func_dep.left if i != y])
                if self.cover_set(x_without_y) == self.cover_set(func_dep.left):
                    return FD(x_without_y, func_dep.right)
            return func_dep

        # Write F as a set of dependencies where each has a single attribute on the right hand side
        F: List[FD] = list(self.split_right().fds)

        # Eliminate trivial dependencies.
        len_f = 0
        while sum([len(x.left) for x in F]) != len_f:
            len_f = sum([len(x.left) for x in F])
            F = [i for i in F if not i.is_trivial()]
            F = [reduce_left_side(self, i) for i in F]
            for f in F:
                if is_implied(F, f):
                    F = [i for i in F if i != f]
                    break

        return set(F)

    def to_bcnf(self) -> None:
        """ Find a Boyce Codd Normal Form of the current FDs object.
        WARING: is not always correct. """
        F = self.canonical()

        # Maximize the right-hand sides of the FDs:
        new_fds = []
        for x_to_y in F:
            new_fd = FD(x_to_y.left, self.cover_set(x_to_y.left) - x_to_y.left)
            new_fds.append(new_fd)

        relations = [set(self.alphabet)]

        def condition_1(x_to_y: FD, r_i: Set) -> bool:
            """ Condition: X ⊆ R_i """
            return x_to_y.left.issubset(r_i)

        def condition_2(x_to_y: FD, r_i: Set) -> bool:
            """ Condition: R_1 ⊈ X^+ """
            return not r_i.issubset(self.cover_set(x_to_y.left))

        def condition_3(x_to_y: FD, r_i: Set) -> bool:
            """ Condition: Y ∩ R_i ≠ ∅ """
            return len(x_to_y.right.intersection(r_i)) > 0

        # Split off violating FD’s one by one:
        change = True
        while change:
            change = False

            for x_to_y in new_fds:
                if change:
                    break

                for i, r_i in enumerate(relations):
                    r_i = relations[i]
                    if (
                        condition_1(x_to_y, r_i)
                        and condition_2(x_to_y, r_i)
                        and condition_3(x_to_y, r_i)
                    ):
                        y_intersect_ri = frozenset(x_to_y.right.intersection(r_i))
                        for j in y_intersect_ri:
                            relations[i].remove(j)

                        relations.append(set(y_intersect_ri.union(x_to_y.left)))

                        change = True
                        break

        return relations

    def to_3nf(self) -> None:
        """ Find a 3rd Normal Form of the current FDs object.
        WARING: is not always correct. """

        def merge_right(F: Set[FD]) -> Set[FD]:
            new_F: Set[FD] = set()

            for fd in F:
                rights_of_same_lefts = map(
                    lambda fd: fd.right, filter(lambda fd2: fd.left == fd2.left, F)
                )

                total_rights: Set = reduce(
                    lambda r1, r2: r1 | r2, rights_of_same_lefts, set()
                )

                new_F |= {FD(fd.left, total_rights)}

            return new_F

        def to_relations(F: Set[FD]) -> Set[FrozenSet[str]]:
            return set(fd.right | fd.left for fd in F)

        def any_contain_minimal(
            relations: Set[FrozenSet[str]], min_keys: List[Set[str]]
        ) -> bool:
            return any(any(key <= rel for key in min_keys) for rel in relations)

        def remove_doubles(relations: Set[FrozenSet[str]]) -> Set[FrozenSet[str]]:
            new_rels: Set[FrozenSet[str]] = set()

            for rel1 in relations:
                duplicate = False
                for rel2 in relations:
                    if not rel1 == rel2 and rel1 <= rel2:
                        duplicate = True

                if not duplicate:
                    new_rels |= {rel1}

            return new_rels

        # Get the canonical FDs and merge their right sides if their left sides are equal
        F: Set[FD] = merge_right(self.canonical())

        # Make relations from the FDs
        relations: Set[FrozenSet[str]] = to_relations(F)

        # Get the min keys
        min_keys = self.minimal_keys(self.alphabet)

        # Verify if any relation contains a minimal key, if not add a relation
        # with a minimal key
        if not any_contain_minimal(relations, min_keys):
            relations |= {min_keys[0]}

        print("Third normal form relations:")
        return remove_doubles(relations)

    def set_is_valid(self, my_set: Set) -> bool:
        """Return true if my_set is contained in the alphabet of the FD object.
        False otherwise."""
        return my_set.issubset(set(self.alphabet))

    def __repr__(self) -> str:
        return str(self)

    def __str__(self) -> str:
        return "\n".join([str(i) for i in self.fds])

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, FDs):
            return NotImplemented

        return self.fds == self.fds


def str_to_fds(string: list, delim: Union[str, List[str]]) -> list:
    """ Turn a string into a list of FDs """
    result = []
    for line in string:
        line_components = line.split(delim)
        result.append(
            [
                set(line_components[0].strip().split(", ")),
                "->",
                set(line_components[1].strip().split(", ")),
            ]
        )

    return [FD(i) for i in result]
