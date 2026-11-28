#include <algorithm>
#include <cmath>
#include <cstdint>
#include <limits>

extern "C" {

// Exact 9-point Gauss-Hermite rank-1 fantasy lookahead for MA-CD-Joint.
// Inputs (row-major contiguous float64):
//   d_zw  : (n_c, n_w)  -- eps - (m_z - m_w)
//   s2_zw : (n_c, n_w)  -- Var(g_{z,w})
//   v_c   : (n_c, n_q)  -- Sigma[comp, queries] / sqrt(obs_var + diag[queries])
//   v_w   : (n_w, n_q)  -- (P Sigma)[:, queries] / sqrt(obs_var + diag[queries])
//   nodes : (n_gh,)     -- Gauss-Hermite standard normal nodes xi_k
//   wts   : (n_gh,)     -- Gauss-Hermite standard normal weights w_k
// Output:
//   out_expected_psi : (n_q,) -- E_xi[ min(1, min_z max_w H_{t+1}^{(x,xi)}(z,w) / beta) ]
void ma_cd_joint_quadrature(
    int32_t n_c,
    int32_t n_w,
    int32_t n_q,
    int32_t n_gh,
    double beta,
    const double* __restrict__ d_zw,
    const double* __restrict__ s2_zw,
    const double* __restrict__ v_c,
    const double* __restrict__ v_w,
    const double* __restrict__ nodes,
    const double* __restrict__ wts,
    double* __restrict__ out_expected_psi
) {
    const double inv_beta = 1.0 / beta;
    const double neg_inf_h = -1.0e6 * beta;

    // Max 32 quadrature points on stack (typically 9)
    double h_root[32];
    double h_z[32];

    for (int32_t x = 0; x < n_q; ++x) {
        for (int32_t k = 0; k < n_gh; ++k) {
            h_root[k] = std::numeric_limits<double>::infinity();
        }
        for (int32_t z = 0; z < n_c; ++z) {
            const double v_cz = v_c[static_cast<std::size_t>(z) * n_q + x];
            const double* d_row = d_zw + static_cast<std::size_t>(z) * n_w;
            const double* s2_row = s2_zw + static_cast<std::size_t>(z) * n_w;
            for (int32_t k = 0; k < n_gh; ++k) {
                h_z[k] = -std::numeric_limits<double>::infinity();
            }
            for (int32_t w = 0; w < n_w; ++w) {
                const double q = v_cz - v_w[static_cast<std::size_t>(w) * n_q + x];
                const double s2p = s2_row[w] - q * q;
                const double d_val = d_row[w];
                if (s2p <= 1.0e-18) {
                    for (int32_t k = 0; k < n_gh; ++k) {
                        const double num = d_val - nodes[k] * q;
                        const double hk = (num >= -1.0e-12) ? beta : neg_inf_h;
                        if (hk > h_z[k]) h_z[k] = hk;
                    }
                } else {
                    const double inv_s = 1.0 / std::sqrt(s2p);
                    const double base = d_val * inv_s;
                    const double slope = -q * inv_s;
                    for (int32_t k = 0; k < n_gh; ++k) {
                        const double hk = base + nodes[k] * slope;
                        if (hk > h_z[k]) h_z[k] = hk;
                    }
                }
            }
            for (int32_t k = 0; k < n_gh; ++k) {
                if (h_z[k] < h_root[k]) h_root[k] = h_z[k];
            }
        }
        double acc = 0.0;
        for (int32_t k = 0; k < n_gh; ++k) {
            double psi = h_root[k] * inv_beta;
            if (psi > 1.0) psi = 1.0;
            acc += wts[k] * psi;
        }
        out_expected_psi[x] = acc;
    }
}

}  // extern "C"
