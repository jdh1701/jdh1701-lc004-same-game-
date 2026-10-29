"""
Corrected (v3) 0/1/All classifier: a relation E (5x5) is "0/1/All" iff every
row has 0, 1, or 5 true entries AND every column has 0, 1, or 5 true entries.
Then sub-classify into universal/empty/forced-row/forced-col/two-fan/matching.
This is the actual Zhang-Yap-Jaffar "0/1/All constraint" property that
PROOF.md Section 3/4.1 needs to hold for the real crossing geometry.
"""
import itertools

def cross(block1, block2):
    tagged = sorted([(x, 0) for x in block1] + [(x, 1) for x in block2])
    runs = 0
    last = None
    for _, tag in tagged:
        if tag != last:
            runs += 1
            last = tag
    return runs >= 4

def local_certs(class_positions):
    certs = []
    for i in range(5):
        pair = {class_positions[i], class_positions[(i+1) % 5]}
        triple = set(class_positions) - pair
        certs.append((pair, triple))
    return certs

def compatible(cert_a, cert_b):
    pa, ta = cert_a
    pb, tb = cert_b
    return not (cross(pa, pb) or cross(pa, tb) or cross(ta, pb) or cross(ta, tb))

def is_zero_one_all(E, n_a=5, n_b=5):
    row_counts = [sum(1 for x in row if x) for row in E]
    col_counts = [sum(1 for i in range(n_a) if E[i][j]) for j in range(n_b)]
    ok = all(c in (0, 1, n_b) for c in row_counts) and all(c in (0, 1, n_a) for c in col_counts)
    return ok, row_counts, col_counts

def classify_shape(E, n_a=5, n_b=5):
    total = sum(sum(1 for x in row if x) for row in E)
    ok, row_counts, col_counts = is_zero_one_all(E, n_a, n_b)
    if not ok:
        return "OTHER-SHAPE", total
    if total == n_a * n_b:
        return "universal", total
    if total == 0:
        return "empty", total
    nfull_rows = sum(1 for c in row_counts if c == n_b)
    nfull_cols = sum(1 for c in col_counts if c == n_a)
    if nfull_rows >= 1 and nfull_cols == 0:
        return f"forced-row(x{nfull_rows})", total
    if nfull_cols >= 1 and nfull_rows == 0:
        return f"forced-col(x{nfull_cols})", total
    if nfull_rows == 1 and nfull_cols == 1:
        return "two-fan", total
    if nfull_rows == 0 and nfull_cols == 0:
        return f"matching(size={total})", total
    return "OTHER-SHAPE", total

def main():
    n = 10
    points = list(range(n))
    shapes = {}
    other_shape_examples = []
    count = 0
    matching_sizes = set()
    for class_a in itertools.combinations(points, 5):
        class_a = set(class_a)
        class_b_set = set(points) - class_a
        a_pos = sorted(class_a)
        b_pos = sorted(class_b_set)
        certs_a = local_certs(a_pos)
        certs_b = local_certs(b_pos)
        E = [[compatible(certs_a[i], certs_b[j]) for j in range(5)] for i in range(5)]
        shape, total = classify_shape(E)
        shapes[shape] = shapes.get(shape, 0) + 1
        count += 1
        if shape.startswith("matching"):
            matching_sizes.add(total)
        if shape == "OTHER-SHAPE":
            other_shape_examples.append((sorted(class_a), E))

    print(f"total arrangements checked: {count}")
    for shape, cnt in sorted(shapes.items(), key=lambda kv: -kv[1]):
        print(f"  {shape}: {cnt}")
    print(f"distinct matching sizes seen: {sorted(matching_sizes)}")
    print(f"OTHER-SHAPE (violates 0/1/All) count: {len(other_shape_examples)}")
    for ex in other_shape_examples[:8]:
        print("COUNTEREXAMPLE:", ex)

if __name__ == "__main__":
    main()
