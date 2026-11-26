// Native -O3 -std=c++17 Exact Analytical Correlated Knowledge Gradient (Frazier-Powell-Dayanik 2009)
// Computes exact underflow-free log(KG_t(x) / c_x) for all candidates x = 0..M-1 in microseconds.
#include <algorithm>
#include <cmath>
#include <cstddef>
#include <limits>
#include <numeric>
#include <vector>

namespace {

constexpr double kLogSqrt2Pi = 0.91893853320467274178;
constexpr double kInvSqrt2 = 0.70710678118654752440;
constexpr double kSqrtPiOver2 = 1.25331413731550025121;

inline double log_expected_pos_normal_scalar(double z) {
    if (z >= 10.0) {
        return std::log(z) + std::log1p(std::exp(-0.5 * z * z - kLogSqrt2Pi) / z);
    }
    if (z >= -12.0) {
        if (z > 0.0) {
            double phi = std::exp(-0.5 * z * z - kLogSqrt2Pi);
            double cdf = 0.5 * std::erfc(-z * kInvSqrt2);
            double v = z * cdf + phi;
            return std::log(v > 1e-300 ? v : 1e-300);
        } else {
            double u = -z * kInvSqrt2;
            double ex = std::erfc(u) * std::exp(u * u);
            double br = 1.0 + z * kSqrtPiOver2 * ex;
            if (br > 1e-12) {
                return -0.5 * z * z - kLogSqrt2Pi + std::log(br);
            }
        }
    }
    // Asymptotic Mills-ratio expansion for z < -12 (error < 3e-9 at -12, < 1e-11 for z <= -15)
    double inv2 = 1.0 / (z * z);
    double ser = inv2 * (1.0 - 3.0 * inv2 * (1.0 - 5.0 * inv2 * (1.0 - 7.0 * inv2 * (1.0 - 9.0 * inv2 * (1.0 - 11.0 * inv2)))));
    if (ser < 1e-300) ser = 1e-300;
    return -0.5 * z * z - kLogSqrt2Pi + std::log(ser);
}

}  // namespace

extern "C" {

void cpp_correlated_kg_log_scores(
    int m,
    const double* means,
    const double* sigma_mat,  // column-major OR row-major symmetric M x M!
    double obs_var,
    const double* costs,
    double* out_log_scores
) {
    const double neg_inf = -std::numeric_limits<double>::infinity();
    if (m <= 1) {
        for (int x = 0; x < m; ++x) out_log_scores[x] = neg_inf;
        return;
    }

    std::vector<int> order;
    order.reserve(static_cast<std::size_t>(m));
    std::vector<double> b_vec(static_cast<std::size_t>(m));
    std::vector<double> hull_a;
    std::vector<double> hull_b;
    std::vector<double> hull_c;
    std::vector<double> lts;
    hull_a.reserve(static_cast<std::size_t>(m));
    hull_b.reserve(static_cast<std::size_t>(m));
    hull_c.reserve(static_cast<std::size_t>(m));
    lts.reserve(static_cast<std::size_t>(m));

    // Pre-find global max intercept (z = 0 pivot is identical across all x!)
    int p_zero = 0;
    double a_zero = means[0];
    for (int i = 1; i < m; ++i) {
        if (means[i] > a_zero) {
            a_zero = means[i];
            p_zero = i;
        }
    }

    int pivots[7];
    double pa[7], pb[7], pc[7];

    for (int x = 0; x < m; ++x) {
        double s_xx = sigma_mat[static_cast<std::size_t>(x) * m + x];
        if (s_xx < 0.0) s_xx = 0.0;
        double denom = s_xx + obs_var;
        if (denom < 1e-18) denom = 1e-18;
        double inv_sd = 1.0 / std::sqrt(denom);

        // Symmetric matrix: row x equals column x in both C and Fortran order!
        const double* row_x = sigma_mat + static_cast<std::size_t>(x) * m;

        // Pass 1 (O(M)): compute slopes b_i and 7 exact tangent pivots at
        // z in {-inf, -6, -2, 0, +2, +6, +inf} for bit-exact dominance pre-filtering.
        int p_min = 0, p_max = 0, p_m6 = 0, p_m2 = 0, p_p2 = 0, p_p6 = 0;
        double b0 = row_x[0] * inv_sd;
        b_vec[0] = b0;
        double b_min_v = b0, a_bmin = means[0];
        double b_max_v = b0, a_bmax = means[0];
        double v_m6 = means[0] - 6.0 * b0;
        double v_m2 = means[0] - 2.0 * b0;
        double v_p2 = means[0] + 2.0 * b0;
        double v_p6 = means[0] + 6.0 * b0;

        for (int i = 1; i < m; ++i) {
            double bi = row_x[i] * inv_sd;
            b_vec[static_cast<std::size_t>(i)] = bi;
            double ai = means[i];
            if (bi < b_min_v || (bi == b_min_v && ai > a_bmin)) {
                b_min_v = bi; a_bmin = ai; p_min = i;
            }
            if (bi > b_max_v || (bi == b_max_v && ai > a_bmax)) {
                b_max_v = bi; a_bmax = ai; p_max = i;
            }
            double t = ai - 6.0 * bi;
            if (t > v_m6) { v_m6 = t; p_m6 = i; }
            t = ai - 2.0 * bi;
            if (t > v_m2) { v_m2 = t; p_m2 = i; }
            t = ai + 2.0 * bi;
            if (t > v_p2) { v_p2 = t; p_p2 = i; }
            t = ai + 6.0 * bi;
            if (t > v_p6) { v_p6 = t; p_p6 = i; }
        }

        if (b_max_v - b_min_v <= 1e-15) {
            out_log_scores[x] = neg_inf;
            continue;
        }

        // Build exact small upper hull of the <= 7 pivot lines
        pivots[0] = p_min; pivots[1] = p_m6; pivots[2] = p_m2;
        pivots[3] = p_zero; pivots[4] = p_p2; pivots[5] = p_p6; pivots[6] = p_max;
        std::sort(pivots, pivots + 7, [&](int i, int j) {
            double bi = b_vec[static_cast<std::size_t>(i)];
            double bj = b_vec[static_cast<std::size_t>(j)];
            if (bi != bj) return bi < bj;
            return means[i] > means[j];
        });
        int np = 0;
        for (int k = 0; k < 7; ++k) {
            int idx = pivots[k];
            double bi = b_vec[static_cast<std::size_t>(idx)];
            double ai = means[idx];
            if (np > 0 && std::abs(bi - pb[np - 1]) <= 1e-15) continue;
            while (np > 0) {
                double c_new = (pa[np - 1] - ai) / (bi - pb[np - 1]);
                if (np > 1 && c_new <= pc[np - 2] + 1e-15) {
                    --np;
                } else {
                    pc[np - 1] = c_new;
                    break;
                }
            }
            pa[np] = ai;
            pb[np] = bi;
            ++np;
        }

        // Exact chord dominance filter: if pb[s] <= b_i <= pb[s+1] and
        // a_i + b_i * pc[s] < pa[s] + pb[s] * pc[s] - margin, line i lies strictly
        // below max(L_s, L_{s+1}) for ALL z in (-inf, +inf) and can never enter the hull.
        order.clear();
        if (np >= 2 && m > 32) {
            double pv[6];
            for (int s = 0; s + 1 < np; ++s) {
                double val_s = pa[s] + pb[s] * pc[s];
                pv[s] = val_s - 1e-12 * (1.0 + std::abs(pa[s]) + std::abs(pb[s] * pc[s]));
            }
            for (int i = 0; i < m; ++i) {
                double bi = b_vec[static_cast<std::size_t>(i)];
                double ai = means[i];
                // Find segment s with pb[s] <= bi <= pb[s+1]
                int s = 0;
                while (s + 2 < np && bi > pb[s + 1]) ++s;
                if (ai + bi * pc[s] >= pv[s]) {
                    order.push_back(i);
                }
            }
        } else {
            order.resize(static_cast<std::size_t>(m));
            std::iota(order.begin(), order.end(), 0);
        }

        std::sort(order.begin(), order.end(), [&](int i, int j) {
            double bi = b_vec[static_cast<std::size_t>(i)];
            double bj = b_vec[static_cast<std::size_t>(j)];
            if (bi != bj) return bi < bj;
            return means[i] > means[j];
        });

        hull_a.clear();
        hull_b.clear();
        hull_c.clear();

        for (int idx : order) {
            double bi = b_vec[static_cast<std::size_t>(idx)];
            double ai = means[idx];
            if (!hull_b.empty() && std::abs(bi - hull_b.back()) <= 1e-15) {
                continue;
            }
            while (!hull_b.empty()) {
                double c_new = (hull_a.back() - ai) / (bi - hull_b.back());
                if (!hull_c.empty() && c_new <= hull_c.back() + 1e-15) {
                    hull_a.pop_back();
                    hull_b.pop_back();
                    hull_c.pop_back();
                } else {
                    hull_c.push_back(c_new);
                    break;
                }
            }
            hull_a.push_back(ai);
            hull_b.push_back(bi);
        }

        std::size_t L = hull_a.size();
        if (L <= 1) {
            out_log_scores[x] = neg_inf;
            continue;
        }

        double max_lt = neg_inf;
        lts.resize(L - 1);
        for (std::size_t k = 0; k + 1 < L; ++k) {
            double db = hull_b[k + 1] - hull_b[k];
            double lt = std::log(db) + log_expected_pos_normal_scalar(-std::abs(hull_c[k]));
            lts[k] = lt;
            if (lt > max_lt) max_lt = lt;
        }
        double sum_exp = 0.0;
        for (std::size_t k = 0; k + 1 < L; ++k) {
            sum_exp += std::exp(lts[k] - max_lt);
        }
        double log_kg = max_lt + std::log(sum_exp);
        out_log_scores[x] = log_kg - std::log(costs[x]);
    }
}

// Fast exact inner-loop evaluator for Bayesian Root-Risk VOI over one candidate x.
// Given current means (M), sensitivity st (M), precomputed zero-mean fluctuation matrix
// fluct (M x N_mu, row-major), y_quantiles (N_y), and packed root-action supports,
// computes E_{j}[ min_a mean_n 1(max_z sample[z, n] - max_{y in S(a)} sample[y, n] > eps) ].
double cpp_voi_eval_candidate(
    int m,
    int k_actions,
    int n_y,
    int n_mu,
    const double* means,
    const double* st,
    const double* fluct,        // row-major M x n_mu
    const double* y_quantiles,  // length n_y
    const int* sup_offsets,     // length k_actions + 1
    const int* sup_indices,     // length sup_offsets[k_actions]
    double epsilon
) {
    std::vector<double> m_next(static_cast<std::size_t>(m));
    std::vector<double> mu_star(static_cast<std::size_t>(n_mu));
    std::vector<double> v_a(static_cast<std::size_t>(n_mu));

    double acc_best_risk = 0.0;
    const double inv_n_mu = 1.0 / static_cast<double>(n_mu);
    const std::size_t stride = static_cast<std::size_t>(n_mu);

    for (int j = 0; j < n_y; ++j) {
        double qj = y_quantiles[j];
        for (int i = 0; i < m; ++i) {
            m_next[static_cast<std::size_t>(i)] = means[i] + qj * st[i];
        }

        // Compute mu_star[n] = max_i (m_next[i] + fluct[i, n])
        const double* f0 = fluct;
        double m0 = m_next[0];
        for (int n = 0; n < n_mu; ++n) {
            mu_star[static_cast<std::size_t>(n)] = m0 + f0[n];
        }
        for (int i = 1; i < m; ++i) {
            const double* fi = fluct + static_cast<std::size_t>(i) * stride;
            double mi = m_next[static_cast<std::size_t>(i)];
            for (int n = 0; n < n_mu; ++n) {
                double val = mi + fi[n];
                if (val > mu_star[static_cast<std::size_t>(n)]) {
                    mu_star[static_cast<std::size_t>(n)] = val;
                }
            }
        }

        // Evaluate each action's risk q_{t+1}(a) and take min_a
        double min_risk = 1.0;
        for (int a = 0; a < k_actions; ++a) {
            int s_beg = sup_offsets[a];
            int s_end = sup_offsets[a + 1];
            int i0 = sup_indices[s_beg];
            const double* fi0 = fluct + static_cast<std::size_t>(i0) * stride;
            double mi0 = m_next[static_cast<std::size_t>(i0)];
            for (int n = 0; n < n_mu; ++n) {
                v_a[static_cast<std::size_t>(n)] = mi0 + fi0[n];
            }
            for (int p = s_beg + 1; p < s_end; ++p) {
                int idx = sup_indices[p];
                const double* fi = fluct + static_cast<std::size_t>(idx) * stride;
                double mi = m_next[static_cast<std::size_t>(idx)];
                for (int n = 0; n < n_mu; ++n) {
                    double val = mi + fi[n];
                    if (val > v_a[static_cast<std::size_t>(n)]) {
                        v_a[static_cast<std::size_t>(n)] = val;
                    }
                }
            }
            int fail_cnt = 0;
            for (int n = 0; n < n_mu; ++n) {
                if (mu_star[static_cast<std::size_t>(n)] - v_a[static_cast<std::size_t>(n)] > epsilon) {
                    ++fail_cnt;
                }
            }
            double r_a = static_cast<double>(fail_cnt) * inv_n_mu;
            if (r_a < min_risk) {
                min_risk = r_a;
                if (fail_cnt == 0) break;
            }
        }
        acc_best_risk += min_risk;
    }
    return acc_best_risk / static_cast<double>(n_y);
}

}  // extern "C"
