"""
Corrected v2: test ACTUAL majority-closure (the real definition) rather than
my flawed '0/1/All over ambient domain 10' shortcut, which was wrong here
because invalid splits zero out whole rows/columns, changing the ambient
counting but not the real closure property.

majority closure: for every (x1,y1),(x2,y2),(x3,y3) in R, the pair
(m(x1,x2,x3), m(y1,y2,y3)) is also in R, where m(a,b,c)=b if b==c else a.
"""
import itertools

def cross(block1, block2):
    tagged = sorted([(x, 0) for x in block1] + [(x, 1) for x in block2])
    runs = 0; last = None
    for _, tag in tagged:
        if tag != last:
            runs += 1; last = tag
    return runs >= 4

def all_splits(class_positions):
    splits = []
    for pair in itertools.combinations(class_positions, 2):
        triple = tuple(x for x in class_positions if x not in pair)
        splits.append((set(pair), set(triple)))
    return splits

def compatible(cert_a, cert_b):
    pa, ta = cert_a
    pb, tb = cert_b
    return not (cross(pa, pb) or cross(pa, tb) or cross(ta, pb) or cross(ta, tb))

def majority(x, y, z):
    return y if y == z else x

def is_majority_closed(true_pairs):
    s = set(true_pairs)
    for (x1, y1), (x2, y2), (x3, y3) in itertools.product(true_pairs, repeat=3):
        mx = majority(x1, x2, x3)
        my = majority(y1, y2, y3)
        if (mx, my) not in s:
            return False, (x1, y1, x2, y2, x3, y3, mx, my)
    return True, None

def covered_by_row_or_col(true_pairs):
    if not true_pairs:
        return True
    xs = set(u for u, v in true_pairs)
    ys = set(v for u, v in true_pairs)
    for x in xs | {None}:
        for y in ys | {None}:
            if x is None and y is None:
                continue
            if all((u == x) or (v == y) for u, v in true_pairs):
                return True
    return False

def main():
    n = 10
    points = list(range(n))
    total = 0
    not_majority_closed = 0
    not_covered = 0
    crossing_count = 0
    nonempty_crossing = 0
    examples_bad = []
    for class_a in itertools.combinations(points, 5):
        class_a = set(class_a)
        class_b_set = set(points) - class_a
        a_pos = sorted(class_a)
        b_pos = sorted(class_b_set)
        splits_a = all_splits(a_pos)
        splits_b = all_splits(b_pos)
        valid_a = [not cross(p, t) for (p, t) in splits_a]
        valid_b = [not cross(p, t) for (p, t) in splits_b]
        assert sum(valid_a) == 5
        assert sum(valid_b) == 5
        true_pairs = []
        for i in range(10):
            for j in range(10):
                if valid_a[i] and valid_b[j] and compatible(splits_a[i], splits_b[j]):
                    true_pairs.append((i, j))
        total += 1
        classes_cross = cross(class_a, class_b_set)
        if classes_cross:
            crossing_count += 1
            if true_pairs:
                nonempty_crossing += 1
        ok, counterex = is_majority_closed(true_pairs)
        if not ok:
            not_majority_closed += 1
            examples_bad.append(("not_majority_closed", sorted(class_a), counterex))
            continue
        if classes_cross:
            if not covered_by_row_or_col(true_pairs):
                not_covered += 1
                examples_bad.append(("not_covered", sorted(class_a), true_pairs))

    print(f"total arrangements: {total}")
    print(f"crossing original classes: {crossing_count}")
    print(f"nonempty AND crossing: {nonempty_crossing}")
    print(f"not majority-closed (CORRECT test): {not_majority_closed}")
    print(f"crossing but NOT covered-by-row-or-col: {not_covered}")
    for e in examples_bad[:8]:
        print("BAD EXAMPLE:", e)

if __name__ == "__main__":
    main()
