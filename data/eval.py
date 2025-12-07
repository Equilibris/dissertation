import matplotlib.pyplot as plt
import numpy as np
from data import slRuns, hpRuns, bigRuns, hpLong, bigLong

X_LAB = "Stream Index"
Y_LAB = "Runtime (ms)"

def plot_performance_comparison():
    sl_array = np.array(slRuns)
    hp_array = np.array(hpRuns)
    big_array = np.array(bigRuns)

    hp_long_array = np.array(hpLong)
    big_long_array = np.array(bigLong)

    sl_means = np.mean(sl_array, axis=0)
    sl_stds = np.std(sl_array, axis=0)

    hp_means = np.mean(hp_array, axis=0)
    hp_stds = np.std(hp_array, axis=0)

    big_means = np.mean(big_array, axis=0)
    big_stds = np.std(big_array, axis=0)

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(16, 8))

    x = np.arange(len(slRuns[0]))
    width = 0.25

    ax1.errorbar(x, hp_means, yerr=hp_stds, label='hpRuns', marker='s', capsize=5)
    ax1.errorbar(x + width, big_means, yerr=big_stds, label='bigRuns', marker='^', capsize=5)
    ax1.errorbar(x - width, sl_means, yerr=sl_stds, label='slRuns', marker='o', capsize=5)

    ax1.set_xlabel(X_LAB)
    ax1.set_ylabel(Y_LAB)
    ax1.set_title('Performance Comparison with Error Bars (1 std)')
    ax1.legend()
    ax1.grid(True, alpha=0.3)

    hp_long_means = np.mean(hp_long_array, axis=0)
    hp_long_stds = np.std(hp_long_array, axis=0)

    big_long_means = np.mean(big_long_array, axis=0)
    big_long_stds = np.std(big_long_array, axis=0)

    x_long = np.arange(len(hpLong[0]))
    width2 = 0.15
    ax2.errorbar(x_long - width2, hp_long_means, yerr=hp_long_stds, label='hpRuns', marker='s', capsize=5, ecolor='C0', alpha=0.1)
    ax2.errorbar(x_long + width2, big_long_means, yerr=big_long_stds, label='bigRuns', marker='^', capsize=5, ecolor='C1', alpha=0.1)

    # Plot lines with full opacity
    ax2.plot(x_long - width2, hp_long_means, marker='s', linestyle='-', label='_nolegend_', color='C0')
    ax2.plot(x_long + width2, big_long_means, marker='^', linestyle='-', label='_nolegend_', color='C1')

    ax2.set_xlabel(X_LAB)
    ax2.set_ylabel(Y_LAB)
    ax2.set_title('HP vs Big Performance Comparison')
    ax2.legend()
    ax2.grid(True, alpha=0.3)

    plt.tight_layout()
    fig.savefig('plot.png', dpi=fig.dpi)

if __name__ == "__main__":
    plot_performance_comparison()
