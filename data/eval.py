from matplotlib import pyplot as plt, rc
import numpy as np
from data import slRuns, hpRuns, bigRuns, preMRuns, smRuns, msRuns

# rc('font', **{'family': 'serif', 'serif': ['Computer Modern']})

HP = "State machine M-Type"
PA = "Progressive approximation"
BIG = "Big"
PREM = "`PreM`-type"
SM = "`SM`-type"
MS = "M. Sammler"

data = {
    PREM : [[i / 1_000_000 for i in x] for x in preMRuns[:3]],
    SM : [[i / 1_000_000 for i in x] for x in smRuns[:3]],
    HP : [[i / 1_000_000 for i in x] for x in hpRuns[:3]],

    PA : [[i / 1_000_000 for i in x] for x in slRuns[:3]],
    MS : [i[:150] for i in msRuns[:3]],

    # SM : smRuns[:3],
    # PREM : preMRuns[:3],
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

# Source - https://stackoverflow.com/a/49601444
# Posted by Ian Hincks, modified by community. See post 'Timeline' for change history
# Retrieved 2026-05-12, License - CC BY-SA 4.0
def lighten_color(color, amount=0.5):
    """
    Lightens the given color by multiplying (1-luminosity) by the given amount.
    Input can be matplotlib color string, hex string, or RGB tuple.

    Examples:
    >> lighten_color('g', 0.3)
    >> lighten_color('#F034A3', 0.6)
    >> lighten_color((.3,.55,.1), 0.5)
    """
    import matplotlib.colors as mc
    import colorsys
    try:
        c = mc.cnames[color]
    except:
        c = color
    c = colorsys.rgb_to_hls(*mc.to_rgb(c))
    return colorsys.hls_to_rgb(c[0], 1 - amount * (1 - c[1]), c[2])

def plot_performance_comparison(data, fname):
    X_LAB = "Stream Index"
    Y_LAB = "Runtime (ms)"

    arrays = {k : np.array(v) for k,v in data.items()}
    means  = {k : np.mean(v, axis=0) for k,v in arrays.items()}
    fit = lambda x, d: np.polynomial.polynomial.Polynomial.fit(np.arange(len(x)), x, d)
    models = {k : fit(v, degrees[k]) for k,v in means.items()}

    fig, ax1 = plt.subplots(1, 1, figsize=(8, 4), dpi = 200)

    for k, mean in means.items():
        alpha = 1
        # v = ax1.plot(means, label=k, alpha = alpha)

        arr = arrays[k]

        model = models[k]
        lab = show[degrees[k]](model.convert().coef)

        # TODO: Try to darken this.
        v = ax1.plot([model(i) for i in range(len(mean))],
            # label=lab
            label=k,
        )
        col = lighten_color(v[0].get_color())

        xs = np.concat([np.arange(len(x)) for x in arr])
        ys = np.concat(arr)
        ax1.scatter(xs, ys,
            color=col,
            alpha=alpha, s=1)

    ax1.set_xlabel(X_LAB)
    ax1.set_ylabel(Y_LAB)
    # ax1.set_title('Performance comparision with fits')
    ax1.legend()
    ax1.grid(True, alpha=0.3)

    plt.tight_layout()
    fig.savefig(fname, dpi=fig.dpi)

    sh = 1000
    print("error:", f"{np.mean(means[HP][sh:] / means[SM][sh:]):.03}")

def sign_test(data, fname):
    SHIFT = 150

    X_LAB = "Stream Index"
    Y_LAB = "Cost per layer (µs)"

    arrays = {k : [(np.array(v)/np.arange(1, len(v)+1))[SHIFT:] for v in v] for k,v in data.items()}
    del arrays[PA]
    del arrays[MS]

    fig, axs = plt.subplot_mosaic(
        [["scatter", "histy"]],
        figsize=(8, 4),
        dpi = 200,
        sharey=True,
        width_ratios=(1, 1)
    )
    scatter = axs["scatter"]
    histy = axs["histy"]

    for k, arr in arrays.items():
        xs = np.concat([np.arange(len(x)) for x in arr]) + SHIFT
        ys = np.concat(arr) * 1000

        histy.hist(ys, bins=20, orientation='horizontal',
            label=k)
        scatter.scatter(xs, ys,
            # color=col,
            alpha=0.1, s=1)

    scatter.set_xlabel(X_LAB)
    scatter.set_ylabel(Y_LAB)
    # ax1.set_title('Performance comparision with fits')
    scatter.grid(True, alpha=0.6)
    histy.legend()

    plt.tight_layout()
    fig.savefig(fname, dpi=fig.dpi)

if __name__ == "__main__":
    plot_performance_comparison(data, "plot.png")
    sign_test(data, "stest.png")
