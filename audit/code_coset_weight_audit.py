"""Independent exact audit of the strengthened binary-code-coset parameters.

This script intentionally uses only the Python standard library.  Fractions are
used for every finite combinatorial identity; Decimal is used only for the two
irrational exponents in the asymptotic parameter audit.
"""

from decimal import Decimal, ROUND_CEILING, ROUND_FLOOR, getcontext
from fractions import Fraction
from itertools import combinations, product


getcontext().prec = 100


def weight(word):
    # Keep compatibility with the Python 3.7 runtime bundled on this machine.
    return bin(word).count("1")


def extend_space(space, vector):
    return frozenset(space | {word ^ vector for word in space})


def all_subspaces(d):
    """Return each linear subspace of F_2^d once (as a frozenset)."""
    spaces = {frozenset({0})}
    for vector in range(1, 1 << d):
        new_spaces = set()
        for space in spaces:
            if vector not in space:
                new_spaces.add(extend_space(space, vector))
        spaces |= new_spaces
    return spaces


def cosets(d, code):
    unseen = set(range(1 << d))
    parts = []
    while unseen:
        representative = min(unseen)
        part = {representative ^ word for word in code}
        parts.append(part)
        unseen -= part
    return parts


def actual_restricted_sum_union(d, code):
    return {
        x + y
        for part in cosets(d, code)
        for x, y in combinations(sorted(part), 2)
    }


def xor_difference_union(d, code):
    return {
        x + (x ^ word)
        for word in code - {0}
        for x in range(1 << d)
    }


def weight_sum(code):
    """S(H) = sum_{0 != h in H} 2^(-wt(h)), exactly."""
    return sum((Fraction(1, 1 << weight(word)) for word in code if word), Fraction())


def image_word(columns, vector):
    result = 0
    for index, column in enumerate(columns):
        if (vector >> index) & 1:
            result ^= column
    return result


def map_weight_sum(columns):
    """Q(T) = sum_{0 != v} 2^(-wt(Tv)); equal to S(im T) if T is injective."""
    m = len(columns)
    return sum(
        (Fraction(1, 1 << weight(image_word(columns, vector)))
         for vector in range(1, 1 << m)),
        Fraction(),
    )


def audit_subspaces(max_d=6):
    total = 0
    equality_cases = 0
    counts = []
    for d in range(1, max_d + 1):
        spaces = all_subspaces(d)
        counts.append(len(spaces))
        for code in spaces:
            actual = actual_restricted_sum_union(d, code)
            by_differences = xor_difference_union(d, code)
            s_value = weight_sum(code)
            normalized_actual = Fraction(len(actual), 1 << d)
            assert actual == by_differences
            assert normalized_actual <= s_value
            if normalized_actual == s_value:
                equality_cases += 1
            total += 1
    return counts, total, equality_cases


def audit_random_map_averages():
    """Exhaustively verify E Q(T)=(2^m-1)(3/4)^d for small d,m."""
    rows = []
    for d in range(1, 6):
        for m in range(1, min(3, d) + 1):
            total = Fraction()
            map_count = 1 << (d * m)
            injective_when_below_one = True
            witnesses_below_one = 0
            for columns in product(range(1 << d), repeat=m):
                q_value = map_weight_sum(columns)
                total += q_value
                if q_value < 1:
                    witnesses_below_one += 1
                    images = {image_word(columns, vector) for vector in range(1 << m)}
                    injective_when_below_one &= len(images) == 1 << m
            enumerated_average = total / map_count
            formula = (2**m - 1) * Fraction(3, 4) ** d
            assert enumerated_average == formula
            assert injective_when_below_one
            rows.append((d, m, map_count, formula, witnesses_below_one))
    return rows


def floor_decimal(value):
    return int(value.to_integral_value(rounding=ROUND_FLOOR))


def nonvacuity_ratio(n, beta):
    """96*N^alpha/N = 96/N^beta, evaluated at high precision."""
    n_dec = Decimal(n)
    return Decimal(96) / (beta * n_dec.ln()).exp()


def audit_parameters(max_d=4096):
    two = Decimal(2)
    beta = (Decimal(4) / Decimal(3)).ln() / two.ln()
    alpha = (Decimal(3) / Decimal(2)).ln() / two.ln()
    assert abs(alpha + beta - 1) < Decimal("1e-95")
    assert abs((alpha * two.ln()).exp() - Decimal(3) / 2) < Decimal("1e-95")
    assert abs((beta * two.ln()).exp() - Decimal(4) / 3) < Decimal("1e-95")

    first_m_nonnegative = None
    first_m_positive = None
    worst_expectation_exact = (Fraction(-1), None)
    worst_class_ratio = (Decimal(-1), None, None)

    for d in range(1, max_d + 1):
        m = floor_decimal(beta * d - 5)
        if m >= 0 and first_m_nonnegative is None:
            first_m_nonnegative = d
        if m >= 1 and first_m_positive is None:
            first_m_positive = d
        if d < 16:
            continue

        expectation_exact = (2**m - 1) * Fraction(3, 4) ** d
        assert expectation_exact < Fraction(1, 32)
        if expectation_exact > worst_expectation_exact[0]:
            worst_expectation_exact = (expectation_exact, d)

        # For fixed d, K/(96*N^alpha) is largest at the smallest allowed N
        # with ceil(log_2 N)=d.  The special d=16 endpoint is N=2^16.
        smallest_n = (1 << 16) if d == 16 else (1 << (d - 1)) + 1
        ambient_int = 1 << d
        assert ambient_int < 2 * smallest_n
        assert 10 * ambient_int < 32 * smallest_n
        k = Decimal(2) ** (d - m)
        n_to_alpha = (alpha * Decimal(smallest_n).ln()).exp()
        class_ratio = k / (Decimal(96) * n_to_alpha)
        assert class_ratio < 1
        if class_ratio > worst_class_ratio[0]:
            worst_class_ratio = (class_ratio, d, smallest_n)

    # Find the exact integer transition for 96*N^alpha <= N.
    low, high = 1, 1 << 16
    while low < high:
        middle = (low + high) // 2
        if nonvacuity_ratio(middle, beta) <= 1:
            high = middle
        else:
            low = middle + 1
    first_nonvacuous_n = low
    assert nonvacuity_ratio(first_nonvacuous_n - 1, beta) > 1
    assert nonvacuity_ratio(first_nonvacuous_n, beta) <= 1

    d16_threshold = Decimal(96) * (Decimal(3) / 2) ** 16
    d16_ratio = d16_threshold / Decimal(1 << 16)
    assert d16_threshold < (1 << 16)

    worst_q, worst_q_d = worst_expectation_exact
    worst_expectation = (
        Decimal(worst_q.numerator) / Decimal(worst_q.denominator),
        worst_q_d,
    )

    return {
        "alpha": alpha,
        "beta": beta,
        "first_m_nonnegative": first_m_nonnegative,
        "first_m_positive": first_m_positive,
        "first_nonvacuous_n": first_nonvacuous_n,
        "ratio_before": nonvacuity_ratio(first_nonvacuous_n - 1, beta),
        "ratio_at": nonvacuity_ratio(first_nonvacuous_n, beta),
        "threshold_before": (
            Decimal(96) * (alpha * Decimal(first_nonvacuous_n - 1).ln()).exp()
        ),
        "threshold_at": (
            Decimal(96) * (alpha * Decimal(first_nonvacuous_n).ln()).exp()
        ),
        "d16_threshold": d16_threshold,
        "d16_ratio": d16_ratio,
        "worst_expectation": worst_expectation,
        "worst_class_ratio": worst_class_ratio,
        "max_d": max_d,
    }


def main():
    counts, total, equality_cases = audit_subspaces()
    print("subspace counts d=1..6:", counts)
    print(f"subspaces checked={total}; equality cases={equality_cases}")

    rows = audit_random_map_averages()
    print("random-map averages (d,m,maps,exact-average,Q<1 maps):")
    for row in rows:
        print(" ", row)

    result = audit_parameters()
    print("alpha=", result["alpha"])
    print("beta=", result["beta"])
    print("first d with m>=0:", result["first_m_nonnegative"])
    print("first d with m>=1:", result["first_m_positive"])
    print("first N with 96*N^alpha <= N:", result["first_nonvacuous_n"])
    print("ratio at N-1:", result["ratio_before"])
    print("ratio at N:", result["ratio_at"])
    print("threshold and ceil at N-1:", result["threshold_before"],
          result["threshold_before"].to_integral_value(rounding=ROUND_CEILING))
    print("threshold and ceil at N:", result["threshold_at"],
          result["threshold_at"].to_integral_value(rounding=ROUND_CEILING))
    print("96*(2^16)^alpha:", result["d16_threshold"])
    print("d=16 nonvacuity ratio:", result["d16_ratio"])
    print(f"largest expectation through d={result['max_d']}:", result["worst_expectation"])
    print(f"largest K/(96*N^alpha) through d={result['max_d']}:",
          result["worst_class_ratio"])


if __name__ == "__main__":
    main()
