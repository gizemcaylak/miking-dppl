#!/usr/bin/env python3
"""Plot logZ convergence vs particle count for the SMC baseline models.

Reads .dat files with columns "particles  mean  std" (produced by
logz_convergence.bash) and draws logZ mean with +/- std error bars on a
log-scaled particle axis, one curve per model.
"""
import argparse
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt


def read_dat(path):
    particles, mean, std = [], [], []
    with open(path) as f:
        next(f)  # header: particles  mean  std
        for line in f:
            line = line.strip()
            if not line:
                continue
            p, m, s = line.split("\t")
            particles.append(int(float(p)))
            mean.append(float(m))
            std.append(float(s))
    return particles, mean, std


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--coalescent", required=True)
    ap.add_argument("--stardecomp", required=True)
    ap.add_argument("--out", required=True)
    args = ap.parse_args()

    series = [
        ("coalescent", args.coalescent, "tab:blue", "o"),
        ("star decomposition", args.stardecomp, "tab:orange", "s"),
    ]

    plt.figure(figsize=(7, 5))
    for label, path, color, marker in series:
        p, m, s = read_dat(path)
        plt.errorbar(p, m, yerr=s, label=label, color=color, marker=marker,
                     capsize=4, linewidth=1.5, markersize=6)

    plt.xscale("log")
    plt.xlabel("number of particles")
    plt.ylabel("log normalizing constant (logZ)")
    plt.title("SMC logZ convergence on toy")
    plt.legend()
    plt.grid(True, which="both", linestyle=":", alpha=0.5)
    plt.tight_layout()
    plt.savefig(args.out, dpi=150)
    print(f"wrote {args.out}")


if __name__ == "__main__":
    main()
