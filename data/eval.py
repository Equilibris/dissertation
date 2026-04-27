import matplotlib.pyplot as plt
import matplotlib.pyplot as plt
import numpy as np
from data import slRuns, hpRuns, bigRuns, preMRuns, smRuns

X_LAB = "Stream Index"
Y_LAB = "Runtime (ms)"

def plot_performance_comparison():
    sl_array = np.array(slRuns)
    hp_array = np.array(hpRuns)
    big_array = np.array(bigRuns)
    prem_array = np.array(preMRuns)
    sm_array = np.array(smRuns)

    sl_means = np.mean(sl_array, axis=0)
    hp_means = np.mean(hp_array, axis=0)
    big_means = np.mean(big_array, axis=0)
    prem_means = np.mean(prem_array, axis=0)
    sm_means = np.mean(sm_array, axis=0)

    fit = lambda x, d: np.polynomial.polynomial.Polynomial.fit(np.arange(len(x)), x, d)
    slm = fit(sl_means, 2)
    hpm = fit(hp_means, 1)
    bim = fit(big_means, 1)
    pim = fit(prem_means, 1)
    smim = fit(sm_means, 1)
    coefs = lambda p: f"{p[1]:.02e} x + {p[2]:.02e} x²"

    fig, ax1 = plt.subplots(1, 1, figsize=(8, 4), dpi = 200)

    alpha = 0.5
    v = ax1.plot(sl_means, label='PA encoding', alpha = alpha)
    ax1.plot([slm(i) for i in range(len(sl_means))], label=coefs(slm.convert().coef), color=v[0].get_color())
    v = ax1.plot(hp_means, label='HpLuM encoding', alpha = alpha)
    ax1.plot([i * hpm.convert().coef[1] for i in range(len(hp_means))], label=f"{hpm.convert().coef[1]:.02e} x", color=v[0].get_color())
    v = ax1.plot(sm_means, label='SM encoding', alpha = alpha)
    ax1.plot([i * smim.convert().coef[1] for i in range(len(big_means))], label=f"{pim.convert().coef[1]:.02e} x", color=v[0].get_color())
    v = ax1.plot(big_means, label='PreM encoding', alpha = alpha)
    ax1.plot([i * bim.convert().coef[1] for i in range(len(big_means))], label=f"{pim.convert().coef[1]:.02e} x", color=v[0].get_color())
    # v = ax1.plot(big_means, label='Big encoding', alpha = alpha)
    # ax1.plot([i * bim.convert().coef[1] for i in range(len(big_means))], label=f"{bim.convert().coef[1]:.02e} x", color=v[0].get_color())

    ax1.set_xlabel(X_LAB)
    ax1.set_ylabel(Y_LAB)
    # ax1.set_title('Performance comparision with fits')
    ax1.legend()
    ax1.grid(True, alpha=0.3)

    plt.tight_layout()
    fig.savefig('plot.svg', dpi=fig.dpi)

    sh = 1000
    print("error:", f"{np.mean(hp_means[sh:] / big_means[sh:]):.03}")

if __name__ == "__main__":
    plot_performance_comparison()
