"""Exact finite checks for Conjectures 2 and 3 in Cigler's q-pol.pdf.

Build both coefficient matrices from the three-term polynomial recurrences
(2.2) and (3.2). Compute their logarithms by direct rational matrix products.
No computer algebra system or third-party package is used.
"""
from fractions import Fraction as F
from math import comb, factorial, prod


def coefficients(size, s, lam):
    rows = [[F(0) for _ in range(size)] for _ in range(size)]
    rows[0][0] = F(1)
    for n in range(1, size):
        for j in range(n + 1):
            if j:
                rows[n][j] += rows[n-1][j-1]
            if n >= 2:
                rows[n][j] += s * lam(n-2) * rows[n-2][j]
    return rows


def matrix_log(a):
    size = len(a)
    lower = [[entry - int(i == j) for j, entry in enumerate(row)]
             for i, row in enumerate(a)]
    total = [[F(0) for _ in range(size)] for _ in range(size)]
    power = lower
    for k in range(1, size):
        if not any(any(row) for row in power):
            break
        factor = F((-1)**(k+1), k)
        for i in range(size):
            for j in range(i + 1):
                total[i][j] += factor * power[i][j]
        power = [[sum((power[i][v]*lower[v][j] for v in range(j, i+1)), F(0))
                  for j in range(size)] for i in range(size)]
    return total


def classical_gamma(n):
    # R(x) = sum c_j x^j, c_1 = 1, and
    # (1+x) R(x) = sum c_j x^j (1-x)^(1-2j).
    # At degree k+1 this determines c_k for k>=2.
    c = [F(0), F(1)]
    for k in range(2, n+1):
        c.append(sum((c[j]*comb(k+j-1, k+1-j) for j in range(1, k)), F(0))
                 / (2-2*k))
    return [factorial(i)*v for i, v in enumerate(c)]


def lambda_classical(i, r, m):
    if i == 0:
        return F(r-1, m+1)
    j = i//2
    if i % 2 == 0:
        return F((m+j)*((j+1)*r-1), (m+2*j)*(m+2*j+1))
    return F(((m+j)*r+1)*(j+1), (m+2*j+1)*(m+2*j+2))


def lambda_q(i, r, q):
    j = i//2
    power, height = (j*r, (j+1)*r-1) if i%2 == 0 else ((j+1)*r-1, (j+1)*r)
    return q**power * sum((q**l for l in range(height)), F(0))


def compare(a, factor, parameters):
    b = matrix_log(a)
    for i in range(len(a)):
        for j in range(len(a)):
            expected = F(0)
            if i > j and (i-j) % 2 == 0:
                expected = a[i][j] * factor(j, (i-j)//2)
            if b[i][j] != expected:
                raise ArithmeticError((parameters, (i, j), b[i][j], expected))
    return len(a)**2


def main():
    counts = [0, 0]
    cases = [0, 0]
    for size in (7, 12, 17, 20):
        g = classical_gamma(size//2)
        if len(g) >= 7 and g[:7] != [0, 1, -1, 3, -14, 80, -468]:
            raise ArithmeticError(g)
        for r in (2, 3, 4, 7):
            for s in (F(1), F(-2, 3)):
                for m in (0, 1, 2, 5, 13):
                    a = coefficients(size, s, lambda i: lambda_classical(i, r, m))
                    counts[0] += compare(
                        a, lambda j, k: g[k] / prod(m+j+l for l in range(1, k)),
                        ("Conjecture 2", size, m, r, s))
                    cases[0] += 1
                for q in (F(1), F(2), F(-1), F(1, 2), F(-2, 3)):
                    a = coefficients(size, s, lambda i: lambda_q(i, r, q))
                    counts[1] += compare(
                        a, lambda j, k: F(1, k)*prod(1-q**(-l*r) for l in range(1,k)),
                        ("Conjecture 3", size, r, q, s))
                    cases[1] += 1
    for guess in range(2):
        print(f"Conjecture {guess+2}: {cases[guess]} matrices, {counts[guess]} entries passed.")
    print("gamma(1..10):", ", ".join(str(x) for x in classical_gamma(10)[1:]))


if __name__ == "__main__":
    main()
