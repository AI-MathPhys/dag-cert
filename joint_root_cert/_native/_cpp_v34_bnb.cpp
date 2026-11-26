// Native -O3 -std=c++17 Outward-Certified Branch-and-Bound & Dual-QP Solver
// for V22/V23/V34 Unknown-Variance Profiled-Likelihood Projections.
//
// Solves:  inf_{u in P}  0.5 * sum_{x=1}^m c_x * log(1 + (k_x/q_x)*(h_x^T u - y_x)^2)
// where P = {u in R^d : A u >= b} is a closed convex polyhedron.
//
// Soundness guarantees (identical to Python reference in `dag_mcts/v9_v34_tracker.py`):
//   1. Upper bound `upper` is ALWAYS evaluated at a strictly verified feasible u in P.
//   2. Lower bound `lower` uses exact interval residual bounds [t_min, t_max], exact
//      concave-secant quadratic minorants log(1+t) >= alpha + beta*t (Prop. V22.2),
//      exact Cholesky-verified regularization shift `0.5 * eps_reg * box_r2` for
//      singular/ill-conditioned Q, and exact Lagrangian weak duality (every lam >= 0
//      gives a valid lower bound) with conservative outward float safety margin.
//   3. Tracks `min_pruned_lb` across all boxes pruned within `tol` of `best_U` so the
//      returned global lower bound NEVER exceeds the true global infimum.

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <limits>
#include <queue>
#include <vector>

namespace {

constexpr double kInf = std::numeric_limits<double>::infinity();

struct BoxNode {
    double lb;
    int64_t tie;
    std::vector<double> lo;
    std::vector<double> hi;
    std::vector<double> u_hint;
};

struct BoxNodeGreater {
    bool operator()(const BoxNode& a, const BoxNode& b) const {
        if (a.lb != b.lb) return a.lb > b.lb;
        return a.tie > b.tie;
    }
};

inline double logaddexp0(double x) {
    if (x > 35.0) return x;
    if (x < -35.0) return 0.0;
    if (x >= 0.0) return x + std::log1p(std::exp(-x));
    return std::log1p(std::exp(x));
}

inline double eval_loss(
    int m, int d,
    const double* u,
    const double* H,
    const double* y,
    const double* c,
    const double* kq
) {
    double acc = 0.0;
    for (int x = 0; x < m; ++x) {
        const double* hx = H + x * d;
        double r = -y[x];
        for (int j = 0; j < d; ++j) r += hx[j] * u[j];
        double t = kq[x] * r * r;
        acc += c[x] * std::log1p(t);
    }
    return 0.5 * acc;
}

inline bool is_poly_feasible(int nc, int d, const double* A, const double* b, const double* u, double eps_feas) {
    for (int i = 0; i < nc; ++i) {
        const double* ai = A + i * d;
        double dot = 0.0;
        for (int j = 0; j < d; ++j) dot += ai[j] * u[j];
        if (dot < b[i] - eps_feas) return false;
    }
    return true;
}

// Cholesky decomposition L * L^T = Q (lower triangular L stored row-major d x d).
// Returns true iff all diagonal entries satisfy L[i,i]^2 > min_diag_sq.
bool cholesky_factor(int d, const double* Q, double* L, double min_diag_sq) {
    std::fill(L, L + d * d, 0.0);
    for (int i = 0; i < d; ++i) {
        for (int j = 0; j <= i; ++j) {
            double s = Q[i * d + j];
            for (int k = 0; k < j; ++k) s -= L[i * d + k] * L[j * d + k];
            if (i == j) {
                if (!(s > min_diag_sq)) return false;
                L[i * d + i] = std::sqrt(s);
            } else {
                L[i * d + j] = s / L[j * d + j];
            }
        }
    }
    return true;
}

// Solve (L * L^T) x = rhs in place (rhs -> x).
inline void cholesky_solve(int d, const double* L, const double* rhs, double* x) {
    for (int i = 0; i < d; ++i) {
        double s = rhs[i];
        const double* Li = L + i * d;
        for (int k = 0; k < i; ++k) s -= Li[k] * x[k];
        x[i] = s / Li[i];
    }
    for (int i = d - 1; i >= 0; --i) {
        double s = x[i];
        for (int k = i + 1; k < d; ++k) s -= L[k * d + i] * x[k];
        x[i] = s / L[i * d + i];
    }
}

// Dual Gauss-Seidel solver for min_{u in B cap P} 0.5 u^T Q u + g^T u + const_val.
// Returns true if not pruned (writes dual_lb and u_sol), false if provably empty or >= cutoff_val.
struct QPWorkspace {
    std::vector<double> Q_reg;
    std::vector<double> L;
    std::vector<double> neg_g;
    std::vector<double> u0;
    std::vector<double> C_mat;   // p x d
    std::vector<double> rhs_vec; // p
    std::vector<double> M_C;     // p x d (row i = Q_reg^{-1} C_i^T)
    std::vector<double> G_d;     // p x p
    std::vector<double> r_d;     // p
    std::vector<double> lam;     // p
    std::vector<double> grad;    // p
    std::vector<double> tmp_d;   // d

    void resize(int d, int p) {
        Q_reg.resize(d * d);
        L.resize(d * d);
        neg_g.resize(d);
        u0.resize(d);
        C_mat.resize(p * d);
        rhs_vec.resize(p);
        M_C.resize(p * d);
        G_d.resize(p * p);
        r_d.resize(p);
        lam.resize(p);
        grad.resize(p);
        tmp_d.resize(d);
    }
};

bool solve_convex_qp_box_poly(
    int d, int nc,
    const double* Q,
    const double* g,
    double const_val,
    const double* A_poly,
    const double* b_poly,
    const double* box_lo,
    const double* box_hi,
    double cutoff_val,
    double& out_lb,
    double* out_u,
    QPWorkspace& ws
) {
    // Fast path 0: quick interval infeasibility check on A_poly u >= b_poly
    for (int i = 0; i < nc; ++i) {
        const double* ai = A_poly + i * d;
        double max_au = 0.0;
        for (int j = 0; j < d; ++j) {
            double aij = ai[j];
            max_au += (aij >= 0.0) ? (aij * box_hi[j]) : (aij * box_lo[j]);
        }
        if (max_au < b_poly[i] - 1e-11) return false;
    }

    double box_r2 = 0.0;
    for (int j = 0; j < d; ++j) {
        double a = box_lo[j] * box_lo[j];
        double b = box_hi[j] * box_hi[j];
        box_r2 += (a > b ? a : b);
    }

    double reg_shift = 0.0;
    for (int i = 0; i < d * d; ++i) ws.Q_reg[i] = Q[i];
    if (!cholesky_factor(d, ws.Q_reg.data(), ws.L.data(), 1e-10)) {
        const double eps_reg = 1e-9;
        for (int i = 0; i < d * d; ++i) ws.Q_reg[i] = Q[i];
        for (int j = 0; j < d; ++j) ws.Q_reg[j * d + j] += eps_reg;
        reg_shift = 0.5 * eps_reg * box_r2;
        if (!cholesky_factor(d, ws.Q_reg.data(), ws.L.data(), 1e-14)) {
            // Ultra-rare numerical fallback: stronger diagonal shift (still 100% sound!)
            const double eps2 = 1e-6;
            for (int i = 0; i < d * d; ++i) ws.Q_reg[i] = Q[i];
            for (int j = 0; j < d; ++j) ws.Q_reg[j * d + j] += eps2;
            reg_shift = 0.5 * eps2 * box_r2;
            if (!cholesky_factor(d, ws.Q_reg.data(), ws.L.data(), 1e-18)) {
                out_lb = 0.0;
                for (int j = 0; j < d; ++j) out_u[j] = 0.5 * (box_lo[j] + box_hi[j]);
                return true;
            }
        }
    }

    for (int j = 0; j < d; ++j) ws.neg_g[j] = -g[j];
    cholesky_solve(d, ws.L.data(), ws.neg_g.data(), ws.u0.data());

    double g_dot_u0 = 0.0;
    for (int j = 0; j < d; ++j) g_dot_u0 += g[j] * ws.u0[j];
    const double v0 = const_val + 0.5 * g_dot_u0 - reg_shift;

    // Fast path 1: unconstrained minimizer u0 feasible in B cap P
    bool u0_ok = true;
    for (int j = 0; j < d; ++j) {
        if (ws.u0[j] < box_lo[j] - 1e-11 || ws.u0[j] > box_hi[j] + 1e-11) {
            u0_ok = false;
            break;
        }
    }
    if (u0_ok && is_poly_feasible(nc, d, A_poly, b_poly, ws.u0.data(), 1e-11)) {
        if (v0 >= cutoff_val) return false;
        out_lb = std::max(0.0, v0 - 1e-11 * std::max(1.0, std::fabs(v0)));
        for (int j = 0; j < d; ++j) {
            out_u[j] = std::min(box_hi[j], std::max(box_lo[j], ws.u0[j]));
        }
        return true;
    }

    // Build combined constraints C u <= rhs: [-A_poly; +I; -I]
    const int p = nc + 2 * d;
    for (int i = 0; i < nc; ++i) {
        const double* ai = A_poly + i * d;
        double* ci = ws.C_mat.data() + i * d;
        for (int j = 0; j < d; ++j) ci[j] = -ai[j];
        ws.rhs_vec[i] = -b_poly[i];
    }
    for (int j = 0; j < d; ++j) {
        double* ci_hi = ws.C_mat.data() + (nc + j) * d;
        double* ci_lo = ws.C_mat.data() + (nc + d + j) * d;
        std::fill(ci_hi, ci_hi + d, 0.0);
        std::fill(ci_lo, ci_lo + d, 0.0);
        ci_hi[j] = 1.0;
        ci_lo[j] = -1.0;
        ws.rhs_vec[nc + j] = box_hi[j];
        ws.rhs_vec[nc + d + j] = -box_lo[j];
    }

    // M_C[i, :] = Q_reg^{-1} C[i, :]^T
    for (int i = 0; i < p; ++i) {
        cholesky_solve(d, ws.L.data(), ws.C_mat.data() + i * d, ws.M_C.data() + i * d);
    }

    // G_d = C * M_C^T (symmetric p x p), r_d = C * u0 - rhs
    for (int i = 0; i < p; ++i) {
        const double* ci = ws.C_mat.data() + i * d;
        double r = -ws.rhs_vec[i];
        for (int k = 0; k < d; ++k) r += ci[k] * ws.u0[k];
        ws.r_d[i] = r;
        ws.grad[i] = r;
        ws.lam[i] = 0.0;
        for (int j = 0; j <= i; ++j) {
            const double* mj = ws.M_C.data() + j * d;
            double s = 0.0;
            for (int k = 0; k < d; ++k) s += ci[k] * mj[k];
            ws.G_d[i * p + j] = s;
            ws.G_d[j * p + i] = s;
        }
    }

    auto eval_dual = [&]() -> double {
        double r_dot_l = 0.0;
        double quad = 0.0;
        for (int i = 0; i < p; ++i) {
            double li = ws.lam[i];
            if (li == 0.0) continue;
            r_dot_l += ws.r_d[i] * li;
            const double* Gi = ws.G_d.data() + i * p;
            double gl = 0.0;
            for (int j = 0; j < p; ++j) {
                if (ws.lam[j] != 0.0) gl += Gi[j] * ws.lam[j];
            }
            quad += li * gl;
        }
        return v0 + r_dot_l - 0.5 * quad;
    };

    const int max_sweeps = 60;
    double dual_val = v0;
    for (int sweep = 0; sweep < max_sweeps; ++sweep) {
        double max_step = 0.0;
        for (int i = 0; i < p; ++i) {
            double g_ii = ws.G_d[i * p + i];
            if (g_ii <= 1e-15) continue;
            double gi = ws.grad[i];
            double li = ws.lam[i];
            if (gi == 0.0 || (li == 0.0 && gi <= 0.0)) continue;
            double l_new = li + gi / g_ii;
            if (l_new < 0.0) l_new = 0.0;
            double dl = l_new - li;
            if (dl != 0.0) {
                ws.lam[i] = l_new;
                const double* Gi = ws.G_d.data() + i * p;
                for (int j = 0; j < p; ++j) ws.grad[j] -= dl * Gi[j];
                double adl = std::fabs(dl);
                if (adl > max_step) max_step = adl;
            }
        }
        if ((sweep % 5 == 4) || max_step < 1e-9) {
            dual_val = eval_dual();
            if (dual_val >= cutoff_val) return false;
            if (max_step < 1e-9) break;
        }
    }

    dual_val = eval_dual();
    if (dual_val >= cutoff_val) return false;

    for (int j = 0; j < d; ++j) {
        double val = ws.u0[j];
        for (int i = 0; i < p; ++i) {
            if (ws.lam[i] != 0.0) val -= ws.M_C[i * d + j] * ws.lam[i];
        }
        out_u[j] = std::min(box_hi[j], std::max(box_lo[j], val));
    }
    out_lb = std::max(0.0, dual_val - 1e-10 * std::max(1.0, std::fabs(dual_val)));
    return true;
}

// Fast feasible local upper-bound polish inside P = {A u >= b} via projected
// Gauss-Newton / backtracking line search using our dual QP projection.
// Every accepted iterate is strictly verified feasible in P (`eps = 1e-9`).
void polish_feasible_upper_bound(
    int m, int d, int nc,
    const double* H,
    const double* y,
    const double* c,
    const double* kq,
    const double* A_poly,
    const double* b_poly,
    double* best_u,
    double& best_U,
    QPWorkspace& ws
) {
    std::vector<double> Q(d * d), g(d), cand(d), big_lo(d, -1e6), big_hi(d, 1e6);
    std::vector<double> w_ir(m);
    for (int it = 0; it < 18; ++it) {
        // IRLS / majorizer convex quadratic around current best_u:
        // log(1 + t) <= log(1 + t0) + (t - t0) / (1 + t0)
        // Minimizing this tight global upper-bound surrogate over P is guaranteed to decrease L(u)!
        std::fill(Q.begin(), Q.end(), 0.0);
        std::fill(g.begin(), g.end(), 0.0);
        double c_val = 0.0;
        for (int x = 0; x < m; ++x) {
            const double* hx = H + x * d;
            double r = -y[x];
            for (int j = 0; j < d; ++j) r += hx[j] * best_u[j];
            double t0 = kq[x] * r * r;
            double wx = c[x] * kq[x] / (1.0 + t0);
            w_ir[x] = wx;
            c_val += 0.5 * wx * y[x] * y[x];
            for (int i = 0; i < d; ++i) {
                g[i] -= wx * y[x] * hx[i];
                for (int j = 0; j < d; ++j) Q[i * d + j] += wx * hx[i] * hx[j];
            }
        }
        // Small Levenberg-Marquardt damping around best_u for stability
        const double damp = 1e-6;
        for (int j = 0; j < d; ++j) {
            Q[j * d + j] += damp;
            g[j] -= damp * best_u[j];
            c_val += 0.5 * damp * best_u[j] * best_u[j];
        }
        double dummy_lb = 0.0;
        // Center big box safely around best_u
        for (int j = 0; j < d; ++j) {
            big_lo[j] = best_u[j] - 1e4;
            big_hi[j] = best_u[j] + 1e4;
        }
        bool ok = solve_convex_qp_box_poly(
            d, nc, Q.data(), g.data(), c_val,
            A_poly, b_poly, big_lo.data(), big_hi.data(),
            kInf, dummy_lb, cand.data(), ws
        );
        if (!ok) break;
        // Ensure strict feasibility & evaluate exact loss (with backtracking toward best_u if needed)
        double step = 1.0;
        bool improved = false;
        std::vector<double> u_try(d);
        for (int ls = 0; ls < 8; ++ls) {
            for (int j = 0; j < d; ++j) u_try[j] = (1.0 - step) * best_u[j] + step * cand[j];
            if (is_poly_feasible(nc, d, A_poly, b_poly, u_try.data(), 1e-8)) {
                double v = eval_loss(m, d, u_try.data(), H, y, c, kq);
                if (v < best_U - 1e-12) {
                    best_U = v;
                    std::copy(u_try.begin(), u_try.end(), best_u);
                    improved = true;
                    break;
                }
            }
            step *= 0.5;
        }
        if (!improved) break;
    }
}

}  // namespace

extern "C" {

struct CppBnBResult {
    double lower;
    double upper;
    int nodes_expanded;
    int used_root_qp_only;
};

// Full outward-certified general-d Branch-and-Bound solver.
// Inputs:
//   m, d, nc: dimensions
//   H (m x d), y (m), c (m), k (m), q (m)
//   A_poly (nc x d), b_poly (nc)
//   u_init (d): verified feasible starting point (e.g. best of feasible_point, warm_u, u_wls)
//   box_lo (d), box_hi (d): initial Lem. V22.1 compact containing box
//   tol: absolute or e-factor log-enclosure tolerance
//   has_early_stop, early_stop_lower
//   has_efactor_shift, efactor_shift
//   root_qp_only (0 or 1), do_polish (0 or 1), max_nodes
// Outputs:
//   out_u (d): feasible witness attaining out_res->upper
//   out_res: CppBnBResult
int run_v34_bnb_certified(
    int m, int d, int nc,
    const double* H,
    const double* y,
    const double* c,
    const double* k,
    const double* q,
    const double* A_poly,
    const double* b_poly,
    const double* u_init,
    const double* box_lo_in,
    const double* box_hi_in,
    int has_basis,
    const int* basis_idx,
    const double* Hb_inv,
    double tol,
    int has_early_stop,
    double early_stop_lower,
    int has_efactor_shift,
    double efactor_shift,
    int root_qp_only,
    int do_polish,
    int max_nodes,
    double* out_u,
    CppBnBResult* out_res
) {
    std::vector<double> kq(m);
    for (int x = 0; x < m; ++x) kq[x] = k[x] / q[x];

    std::vector<double> best_u(u_init, u_init + d);
    double best_U = eval_loss(m, d, best_u.data(), H, y, c, kq.data());

    const int p = nc + 2 * d;
    QPWorkspace ws;
    ws.resize(d, p);

    if (do_polish) {
        polish_feasible_upper_bound(m, d, nc, H, y, c, kq.data(), A_poly, b_poly, best_u.data(), best_U, ws);
    }

    if (best_U <= tol) {
        std::copy(best_u.begin(), best_u.end(), out_u);
        out_res->lower = 0.0;
        out_res->upper = best_U;
        out_res->nodes_expanded = 1;
        out_res->used_root_qp_only = 1;
        return 0;
    }

    // Re-tighten initial Lem. V22.1 containing box using post-polish best_U if basis is finite!
    std::vector<double> root_lo(box_lo_in, box_lo_in + d);
    std::vector<double> root_hi(box_hi_in, box_hi_in + d);
    if (has_basis) {
        std::vector<double> rb(d);
        bool all_fin = true;
        for (int i = 0; i < d; ++i) {
            int x = basis_idx[i];
            if (c[x] <= 1e-15) { all_fin = false; break; }
            double arg = 2.0 * best_U / c[x];
            if (arg >= 50.0) { all_fin = false; break; }
            double tx = (arg <= 1e-10) ? std::max(0.0, arg) : std::expm1(arg);
            rb[i] = std::sqrt((q[x] / k[x]) * tx);
        }
        if (all_fin) {
            for (int i = 0; i < d; ++i) {
                double ctr = 0.0;
                double rad = 0.0;
                const double* row = Hb_inv + i * d;
                for (int j = 0; j < d; ++j) {
                    ctr += row[j] * y[basis_idx[j]];
                    rad += std::fabs(row[j]) * rb[j];
                }
                root_lo[i] = ctr - rad - 1e-6;
                root_hi[i] = ctr + rad + 1e-6;
            }
        }
    }

    auto efactor_gap_ok = [&](double lb_val, double ub_val) -> bool {
        if (!has_efactor_shift) return false;
        double f_ub = logaddexp0(ub_val - efactor_shift);
        double f_lb = logaddexp0(lb_val - efactor_shift);
        return (f_ub - f_lb) <= tol;
    };

    // Precompute pos_H and neg_H for ultra-fast interval arithmetic
    std::vector<double> pos_H(m * d), neg_H(m * d);
    for (int i = 0; i < m * d; ++i) {
        pos_H[i] = (H[i] > 0.0) ? H[i] : 0.0;
        neg_H[i] = (H[i] < 0.0) ? H[i] : 0.0;
    }

    std::vector<double> t_min(m), t_max(m), alpha(m), beta(m), w_q(m);
    std::vector<double> Q(d * d), g(d);

    auto eval_box_lower = [&](const double* b_lo, const double* b_hi, double& lb_out, double* u_out) -> bool {
        double int_lb = 0.0;
        for (int x = 0; x < m; ++x) {
            const double* ph = pos_H.data() + x * d;
            const double* nh = neg_H.data() + x * d;
            double r_lo = -y[x];
            double r_hi = -y[x];
            for (int j = 0; j < d; ++j) {
                r_lo += ph[j] * b_lo[j] + nh[j] * b_hi[j];
                r_hi += ph[j] * b_hi[j] + nh[j] * b_lo[j];
            }
            double r_abs_min = 0.0;
            if (r_lo > 0.0) r_abs_min = r_lo;
            else if (-r_hi > 0.0) r_abs_min = -r_hi;
            double r_abs_max = std::max(std::fabs(r_lo), std::fabs(r_hi));
            double tmin = kq[x] * r_abs_min * r_abs_min;
            double tmax = kq[x] * r_abs_max * r_abs_max;
            if (c[x] > 1e-15) {
                double arg = 2.0 * best_U / c[x];
                if (arg < 50.0) {
                    double t_cap = std::expm1(arg);
                    if (tmin > t_cap + 1e-9) return false;  // Box strictly above incumbent U!
                    if (tmax > t_cap) tmax = t_cap;
                }
            }
            t_min[x] = tmin;
            t_max[x] = tmax;
            int_lb += 0.5 * c[x] * std::log1p(tmin);
        }

        if (int_lb >= best_U - 1e-12) {
            lb_out = int_lb;
            for (int j = 0; j < d; ++j) u_out[j] = 0.5 * (b_lo[j] + b_hi[j]);
            return true;
        }

        // Exact concave secant minorant: log(1+t) >= alpha[x] + beta[x]*t on [t_min, t_max]
        std::fill(Q.begin(), Q.end(), 0.0);
        std::fill(g.begin(), g.end(), 0.0);
        double const_val = 0.0;
        for (int x = 0; x < m; ++x) {
            double diff = t_max[x] - t_min[x];
            double l_lo = std::log1p(t_min[x]);
            double l_hi = std::log1p(t_max[x]);
            double bx = (diff > 1e-11) ? ((l_hi - l_lo) / diff) : (1.0 / (1.0 + t_min[x]));
            double ax = l_lo - bx * t_min[x];
            double wq = c[x] * bx * kq[x];
            const_val += 0.5 * c[x] * ax + 0.5 * wq * y[x] * y[x];
            const double* hx = H + x * d;
            for (int i = 0; i < d; ++i) {
                double w_hi = wq * hx[i];
                g[i] -= w_hi * y[x];
                for (int j = 0; j < d; ++j) Q[i * d + j] += w_hi * hx[j];
            }
        }

        double lb_qp = 0.0;
        if (!solve_convex_qp_box_poly(
                d, nc, Q.data(), g.data(), const_val,
                A_poly, b_poly, b_lo, b_hi, best_U + 1e-6, lb_qp, u_out, ws)) {
            return false;
        }
        lb_out = std::max(int_lb, lb_qp);
        return true;
    };

    std::vector<double> u_qp(d);
    double root_lb = 0.0;
    if (!eval_box_lower(root_lo.data(), root_hi.data(), root_lb, u_qp.data())) {
        std::copy(best_u.begin(), best_u.end(), out_u);
        out_res->lower = best_U;
        out_res->upper = best_U;
        out_res->nodes_expanded = 1;
        out_res->used_root_qp_only = 1;
        return 0;
    }

    if (is_poly_feasible(nc, d, A_poly, b_poly, u_qp.data(), 1e-9)) {
        double v_qp = eval_loss(m, d, u_qp.data(), H, y, c, kq.data());
        if (v_qp < best_U) {
            best_U = v_qp;
            std::copy(u_qp.begin(), u_qp.end(), best_u.begin());
        }
    }
    if (root_lb > best_U) root_lb = best_U;

    if (root_qp_only
        || (best_U - root_lb <= tol)
        || efactor_gap_ok(root_lb, best_U)
        || (has_early_stop && root_lb >= early_stop_lower)) {
        std::copy(best_u.begin(), best_u.end(), out_u);
        out_res->lower = std::max(0.0, root_lb);
        out_res->upper = best_U;
        out_res->nodes_expanded = 1;
        out_res->used_root_qp_only = 1;
        return 0;
    }

    std::priority_queue<BoxNode, std::vector<BoxNode>, BoxNodeGreater> heap;
    int64_t tie = 0;
    heap.push(BoxNode{root_lb, tie, std::move(root_lo), std::move(root_hi), u_qp});
    double min_pruned_lb = kInf;
    int nodes = 1;
    std::vector<double> ch_u(d);

    while (!heap.empty() && nodes < max_nodes) {
        BoxNode cur = heap.top();
        heap.pop();

        double global_lb_now = std::min({cur.lb, min_pruned_lb, best_U});
        if ((best_U - global_lb_now <= tol) || efactor_gap_ok(global_lb_now, best_U)) {
            std::copy(best_u.begin(), best_u.end(), out_u);
            out_res->lower = std::max(0.0, global_lb_now);
            out_res->upper = best_U;
            out_res->nodes_expanded = nodes;
            out_res->used_root_qp_only = 0;
            return 0;
        }
        if (has_early_stop && global_lb_now >= early_stop_lower) {
            std::copy(best_u.begin(), best_u.end(), out_u);
            out_res->lower = std::max(0.0, global_lb_now);
            out_res->upper = best_U;
            out_res->nodes_expanded = nodes;
            out_res->used_root_qp_only = 0;
            return 0;
        }
        if (cur.lb >= best_U - tol) {
            if (cur.lb < min_pruned_lb) min_pruned_lb = cur.lb;
            continue;
        }

        int split_j = 0;
        double max_w = cur.hi[0] - cur.lo[0];
        for (int j = 1; j < d; ++j) {
            double w = cur.hi[j] - cur.lo[j];
            if (w > max_w) {
                max_w = w;
                split_j = j;
            }
        }
        if (max_w <= 1e-11) {
            if (cur.lb < min_pruned_lb) min_pruned_lb = cur.lb;
            continue;
        }

        double mid = 0.5 * (cur.lo[split_j] + cur.hi[split_j]);
        if (cur.u_hint[split_j] >= cur.lo[split_j] + 0.2 * max_w
            && cur.u_hint[split_j] <= cur.hi[split_j] - 0.2 * max_w) {
            mid = cur.u_hint[split_j];
        }

        for (int side = 0; side < 2; ++side) {
            std::vector<double> c_lo = cur.lo;
            std::vector<double> c_hi = cur.hi;
            if (side == 1) c_lo[split_j] = mid;
            else c_hi[split_j] = mid;
            ++nodes;
            double ch_lb = 0.0;
            if (!eval_box_lower(c_lo.data(), c_hi.data(), ch_lb, ch_u.data())) {
                continue;
            }
            if (is_poly_feasible(nc, d, A_poly, b_poly, ch_u.data(), 1e-9)) {
                double ch_val = eval_loss(m, d, ch_u.data(), H, y, c, kq.data());
                if (ch_val < best_U) {
                    best_U = ch_val;
                    std::copy(ch_u.begin(), ch_u.end(), best_u.begin());
                }
            }
            if (ch_lb < best_U - tol) {
                ++tie;
                heap.push(BoxNode{ch_lb, tie, std::move(c_lo), std::move(c_hi), ch_u});
            } else {
                if (ch_lb < min_pruned_lb) min_pruned_lb = ch_lb;
            }
        }
    }

    double rem_lb = heap.empty() ? kInf : heap.top().lb;
    double global_lb = std::min({best_U, min_pruned_lb, rem_lb});
    std::copy(best_u.begin(), best_u.end(), out_u);
    out_res->lower = std::max(0.0, global_lb);
    out_res->upper = best_U;
    out_res->nodes_expanded = nodes;
    out_res->used_root_qp_only = 0;
    return 0;
}

}  // extern "C"
