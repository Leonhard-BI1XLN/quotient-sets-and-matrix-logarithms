"""Exhaust the two cross-block quotient formulas in the symmetric groups S3 to S6."""

from array import array
from collections import Counter
from itertools import permutations, product
from time import perf_counter


def symmetric_group_tables(degree):
    elements = list(permutations(range(degree)))
    index = {element: position for position, element in enumerate(elements)}
    multiply = [
        array("H", (index[tuple(left[i] for i in right)] for right in elements))
        for left in elements
    ]
    inverse = [row.index(0) for row in multiply]
    return multiply, inverse


def verify(degree):
    multiply, inverse = symmetric_group_tables(degree)
    order = len(inverse)
    result = Counter()
    for g in range(1, order):
        g_inv = inverse[g]
        involution = g == g_inv
        powers = {0: 0, 1: g, -1: g_inv}
        exponents = (0, 1) if involution else (-1, 0, 1)
        for z in range(order):
            z_inv = inverse[z]
            conjugate = multiply[multiply[z][g]][z_inv]
            if conjugate in (g, g_inv):
                continue

            # Work directly with the blocks {1,g} and {z,zg}, using all eight
            # oriented cross-products without any analytic simplification.
            block1 = (0, g)
            block2 = (z, multiply[z][g])
            pairs = list(product(block1, block2)) + list(product(block2, block1))
            right = {multiply[x][inverse[y]] for x, y in pairs}
            left = {multiply[inverse[x]][y] for x, y in pairs}
            matches = [
                (a, b)
                for a, b in product(exponents, repeat=2)
                if multiply[multiply[powers[a]][z]][powers[b]] == z_inv
            ]

            if involution:
                assert len(matches) <= 1, (degree, g, z, matches)
                predicted = (4 - len(matches), 8 - 4 * len(matches))
                disparity = -4 + 3 * len(matches)
            else:
                assert all((a == 0) == (b == 0) for a, b in matches)
                weight = sum((2 - abs(a)) * (2 - abs(b)) for a, b in matches)
                predicted = (6 - len(matches), 8 - weight)
                disparity = -2 + 3 * (z == z_inv)
            assert predicted == (len(right), len(left)), (
                degree, g, z, matches, predicted, right, left
            )
            assert len(right) - len(left) == disparity
            result[(involution, disparity)] += 1
    return result


if __name__ == "__main__":
    started = perf_counter()
    total = Counter()
    for degree in range(3, 7):
        counts = verify(degree)
        total.update(counts)
        print(f"S{degree}: {sum(counts.values()):,} qualified pairs, {dict(counts)}")
    assert set(total) == {(True, -4), (True, -1), (False, -2), (False, 1)}
    print(f"Total: {sum(total.values()):,} qualified pairs, all four cases verified.")
    print(f"Elapsed: {perf_counter() - started:.1f} seconds.")
