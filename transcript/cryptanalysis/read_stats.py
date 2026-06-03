import statistics


if __name__=="__main__":

    data = {}
    for p in [3, 7, 11, 19]:
        filename = f"brute_p{p}.txt"
        visited_counts = []
        dipped_counts = []
        with open("stats/" + filename, "r") as f:
            next(f)
            for l in f:
                line = l.strip()
                visited, dipped = line.split(",")
                visited_counts.append(int(visited))
                dipped_counts.append(int(dipped))

        data[p] = {
            "mean_v": statistics.mean(visited_counts),
            "med_v": int(statistics.median(visited_counts)),
            "mean_d": statistics.mean(dipped_counts),
            "med_d": int(statistics.median(dipped_counts)),
        }

    # ---- build LaTeX table ----
    primes = sorted(data.keys())

    def row(label, key):
        return (
            label + " & " +
            " & ".join(
                (f"{data[p][key]:.2f}" if "mean" in key else f"{data[p][key]:d}")
                for p in primes
            ) +
            r" \\"
        )

    latex = []
    latex.append(r"\begin{tabular}{l" + "c" * len(primes) + "}")
    latex.append(r"\toprule")

    # header
    latex.append(" & " + " & ".join("p = " + str(p) for p in primes) + r" \\")
    latex.append(r"\midrule")

    # rows
    latex.append(row("Avg. vertices visited", "mean_v"))
    latex.append(row("Median vertices visited", "med_v"))
    latex.append(row("Mean dipped", "mean_d"))
    latex.append(row("Median dipped", "med_d"))

    latex.append(r"\bottomrule")
    latex.append(r"\end{tabular}")

    latex_output = "\n".join(latex)

    print(latex_output)
