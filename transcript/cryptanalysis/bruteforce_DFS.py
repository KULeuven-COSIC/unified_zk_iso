from build_graph import *
import random

from collections import defaultdict

def dfs_until_counterfit_path(start_theta):
    """
    DFS traversal that stops as soon as we move from a non-Riemann
    theta point to one satisfying the Riemann relation.

    Parameters
    ----------
    start_theta:
        Initial theta point

    Returns
    -------
    result : dict
        {
            "found": bool,
            "path": list of vertices,
            "target": vertex or None,
            "visited_count": int,
            "visited": set,
        }
    """

    start = normalize_tuple(start_theta)

    visited = set()

    visited_count = 0

    def dfs(theta, depth, path):

        nonlocal visited_count

        visited.add(theta)
        visited_count += 1

        theta_is_riemann = check_riemann(theta)

        nbrs = list(radical_step_normalized(theta))
        random.shuffle(nbrs)

        for tt in nbrs:

            tt_is_riemann = check_riemann(tt)
            # STOP CONDITION:
            # current node fails Riemann,
            # next node satisfies it
            if (not theta_is_riemann) and tt_is_riemann:

                return {
                    "found": True,
                    "path": path + [tt],
                    "target": tt,
                    "visited_count": visited_count,
                    "visited": visited,
                }

            if tt not in visited:

                result = dfs(
                    tt,
                    depth + 1,
                    path + [tt]
                )

                if result is not None:
                    return result

        return None

    result = dfs(start, 0, [start])

    if result is None:
        return {
            "found": False,
            "path": [],
            "target": None,
            "visited_count": visited_count,
            "visited": visited,
        }

    return result


from collections import deque
import random

def bfs_until_counterfit_path(start_theta):
    """
    BFS traversal that stops as soon as we move from a non-Riemann
    theta point to one satisfying the Riemann relation.

    Returns
    -------
    result : dict
        {
            "found": bool,
            "path": list of vertices,
            "target": vertex or None,
            "visited_count": int,
            "visited": set,
        }
    """

    start = normalize_tuple(start_theta)

    if start is None:
        raise ValueError("Start theta normalizes to zero vector.")

    visited = {start}

    # Queue stores:
    # (current_theta, path_to_theta)
    q = deque([(start, [start])])

    visited_count = 0

    while q:

        theta, path = q.popleft()

        visited_count += 1

        theta_is_riemann = check_riemann(theta)

        nbrs = list(radical_step_normalized(theta))
        random.shuffle(nbrs)

        for tt in nbrs:

            tt_is_riemann = check_riemann(tt)

            # STOP CONDITION:
            # current node fails Riemann,
            # next node satisfies it
            if (not theta_is_riemann) and tt_is_riemann:

                return {
                    "found": True,
                    "path": path + [tt],
                    "target": tt,
                    "visited_count": visited_count,
                    "visited": visited,
                }

            if tt not in visited:

                visited.add(tt)

                q.append(
                    (tt, path + [tt])
                )

    return {
        "found": False,
        "path": [],
        "target": None,
        "visited_count": visited_count,
        "visited": visited,
    }



if __name__=="__main__":
    reps = 100
    from tqdm import tqdm
    for p in Primes()[1:10]:
        filename = f"brute_p{p}.txt"
        if p % 4 != 3:
            continue
        Fp2 = GF(p**2, name="i", modulus=[1, 0, 1])
        E0 = EllipticCurve(Fp2, [1, 0])

        assert E0.is_supersingular()
        theta0 = curve_to_theta_3(E0, E0, E0)

        print(f"running for p = {p}")
        with open("stats/" + filename, "w") as f:
            f.write("visited_count, solution_dipped_outside_for\n")
            for _ in tqdm(range(reps)):
                result = dfs_until_counterfit_path(theta0)

                num_false = 0
                for tt in result["path"][::-1][1:]:
                    if check_riemann(tt):
                        break
                    num_false += 1
                f.write(f"{result["visited_count"]}, {num_false}\n")
        
        
    
    
