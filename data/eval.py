import matplotlib.pyplot as plt
import matplotlib.pyplot as plt
import numpy as np
from data import slRuns, hpRuns, bigRuns, preMRuns, smRuns, msRuns

X_LAB = "Stream Index"
Y_LAB = "Runtime (ms)"

HP = "HpLuM"
PA = "PA encoding"
BIG = "Big"
PREM = "PreM-type"
SM = "SM encoding"
MS = "MS implementation"

data = {
    PREM : preMRuns[:3],
    SM : smRuns[:3],
    HP : hpRuns[:3],
    MS : [i[:200] for i in msRuns[:3]],
    PA : slRuns[:3],
    # BIG : bigRuns[:3],
}
degrees = {
    PA : 2,
    HP : 1,
    BIG : 1,
    PREM : 1,
    SM : 1,
    MS : 2,
}

show = [
    lambda _: f"1",
    lambda p: f"{p[1]:.02e} x",
    lambda p: f"{p[1]:.02e} x + {p[2]:.02e} x²"
]

def plot_performance_comparison(data, fname):
    arrays = {k : np.array(v) for k,v in data.items()}
    means  = {k : np.mean(v, axis=0) for k,v in arrays.items()}
    fit = lambda x, d: np.polynomial.polynomial.Polynomial.fit(np.arange(len(x)), x, d)
    models = {k : fit(v, degrees[k]) for k,v in means.items()}

    fig, ax1 = plt.subplots(1, 1, figsize=(8, 4), dpi = 200)

    for k, mean in means.items():
        alpha = .02
        # v = ax1.plot(means, label=k, alpha = alpha)

        arr = arrays[k]

        model = models[k]
        lab = show[degrees[k]](model.convert().coef)

        v = ax1.plot([model(i) for i in range(len(mean))], label=lab)
        col = v[0].get_color()

        xs = np.concat([np.arange(len(x)) for x in arr])
        ys = np.concat(arr)
        ax1.scatter(xs, ys, label=k, color=col, alpha=alpha, s=.5)

    ax1.set_xlabel(X_LAB)
    ax1.set_ylabel(Y_LAB)
    # ax1.set_title('Performance comparision with fits')
    ax1.legend()
    ax1.grid(True, alpha=0.3)

    plt.tight_layout()
    fig.savefig(fname, dpi=fig.dpi)

    sh = 1000
    print("error:", f"{np.mean(means[HP][sh:] / means[SM][sh:]):.03}")

if __name__ == "__main__":
    plot_performance_comparison(data, "plot.png")
