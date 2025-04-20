pub(crate) mod srs;
pub(crate) mod util;
use ark_poly_commit::kzg10::Proof;
use ark_poly_commit::kzg10::VerifierKey;
use crate::{
    pcs::{
        multilinear_kzg::{MultilinearKzgPCS, MultilinearKzgProof},
        prelude::PCSError,
        PolynomialCommitmentScheme,
    },
    BatchProof,
};
use rand_chacha::ChaCha8Rng;
use ark_poly_commit::PCRandomness;
use crate::pcs::Samaritan::util::*;
use ark_bls12_381::{Bls12_381, Fr, FrConfig};
use ark_ec::pairing::Pairing;
use ark_ff::{Field, MontBackend, One, PrimeField, UniformRand, Zero};
use ark_poly::{
    univariate::DensePolynomial, DenseMultilinearExtension, DenseUVPolynomial,
    MultilinearExtension, Polynomial,
};
use ark_poly_commit::kzg10::{self, Commitment, Powers, Randomness, UniversalParams, KZG10, };
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{
    borrow::Borrow,
    end_timer, format, log2,
    marker::PhantomData,
    rand::{Rng, SeedableRng},
    start_timer,
    string::ToString,
    sync::Arc,
    test_rng, vec,
    vec::Vec,
};

use std::{borrow::Cow, collections::HashMap};
use transcript::IOPTranscript;

type F = <Bls12_381 as Pairing>::ScalarField;
type Poly = DensePolynomial<F>;
type KZG10Scheme = KZG10<Bls12_381, Poly>;
type MultiPoly<F> = HashMap<(usize, usize), F>;

#[derive(CanonicalSerialize, CanonicalDeserialize, Clone, Debug, PartialEq, Eq)]
pub struct SamaritanProof {
    commitments: Vec<Commitment<Bls12_381>>,
    evaluations: Vec<F>,
    batch_proof: Option<Vec<u8>>,
}

pub struct SamaritanPCS<E: Pairing> {
    phantom: PhantomData<E>,
}

impl<E: Pairing<ScalarField = ark_ff::Fp<MontBackend<FrConfig, 4>, 4>>>
    PolynomialCommitmentScheme<E> for SamaritanPCS<E>
{
    // Parameters
    type ProverParam = UniversalParams<Bls12_381>;
    type VerifierParam = UniversalParams<Bls12_381>;
    type SRS = UniversalParams<Bls12_381>;
    // Polynomial and its associated types
    type Polynomial = DensePolynomial<F>;
    type Point = Vec<F>;
    type Evaluation = F;
    // Commitments and proofs
    type Commitment = Commitment<Bls12_381>;
    type Proof = SamaritanProof;
    type BatchProof = ();
 

    fn gen_srs_for_testing<R: Rng>(rng: &mut R, log_size: usize) -> Result<UniversalParams<Bls12_381>, PCSError> {
        let setup_timer = start_timer!(|| "SamaritanPCS setup");
        let max_degree = 1 << (log_size + 1);
        let srs = KZG10::<Bls12_381, Poly>::setup(max_degree, false, rng)
            .map_err(|e| PCSError::InvalidParameters(format!("Setup failed: {:?}", e)))?;
        end_timer!(setup_timer);
        Ok(srs)
    }

    /// Trim the universal parameters to specialize the public parameters.
    /// Input both `supported_log_degree` for univariate and
    /// `supported_num_vars` for multilinear.
    fn trim(
        srs: impl Borrow<Self::SRS>,
        supported_degree: Option<usize>,
        supported_num_vars: Option<usize>,
    ) -> Result<(Self::ProverParam, Self::VerifierParam), PCSError> {
        unimplemented!();
    }

    fn commit(
        prover_param: impl Borrow<Self::ProverParam>,
        poly: &Self::Polynomial,
    ) -> Result<Self::Commitment, PCSError> {
        let prover_param = prover_param.borrow();
        let commit_timer = start_timer!(|| "commit");

        let (comm, rand) = commit(prover_param, poly);
        end_timer!(commit_timer);
        Ok(comm)
    }

    /// On input a polynomial `p` and a point `point`, outputs a proof for the
    /// same. This function does not need to take the evaluation value as an
    /// input.
    ///
    /// This function takes 2^{num_var +1} number of scalar multiplications over
    /// G1:
    /// - it prodceeds with `num_var` number of rounds,
    /// - at round i, we compute an MSM for `2^{num_var - i + 1}` number of G2
    ///   elements.
    fn open(
        pp: impl Borrow<Self::ProverParam>,
        f_hat: &Self::Polynomial,
        z: &Self::Point,
    ) -> Result<(Self::Proof, Self::Evaluation), PCSError>  {
        let mut f_hat_coeffs = f_hat.coeffs();
        let miu = z.len() as u32;
        let mut evaluations = vec![F::zero(); 1 << miu];
        for i in 0..(1 << miu) {
            let index = (0..miu)
                .map(|k| (i >> k) & 1)
                .fold(0, |acc, bit| (acc << 1) | bit);
            evaluations[index] = f_hat_coeffs[i];
        }
        println!("OK111");
        // println!("evaluations{:?}",evaluations);
        let f_poly = DenseMultilinearExtension::from_evaluations_vec(miu as usize, evaluations);
       let (proof,evaluation)=open_internal::<E>(pp.borrow(), f_hat_coeffs, &f_poly, miu, z.to_vec())?;
       Ok((proof,evaluation))
    }

    /// Input a list of multilinear extensions, and a same number of points, and
    /// a transcript, compute a multi-opening for all the polynomials.
    // fn multi_open(
    //     _prover_param: impl Borrow<Self::ProverParam>,
    //     _polynomials: Vec<Self::Polynomial>,
    //     _advices: &[Self::ProverCommitmentAdvice],
    //     _points: &[Self::Point],
    //     _evals: &[Self::Evaluation],
    //     _transcript: &mut IOPTranscript<E::ScalarField>,
    // ) -> Result<Self::BatchProof, PCSError> {
    //     unimplemented!();
    // }

    /// Verifies that `value` is the evaluation at `x` of the polynomial
    /// committed inside `comm`.
    ///
    /// This function takes
    /// - num_var number of pairing product.
    /// - num_var number of MSM
    fn verify(
        verifier_param: &Self::VerifierParam,
        commitment: &Self::Commitment,
        z: &Self::Point,
        value: &E::ScalarField,
        proof: &Self::Proof,
    ) -> Result<bool, PCSError> {
        verify_internal::<Bls12_381>(commitment,verifier_param, z.to_vec(), proof)
    }

    // Verifies that `value_i` is the evaluation at `x_i` of the polynomial
    //`poly_i` committed inside `comm`.
//     fn batch_verify(
//         verifier_param: &Self::VerifierParam,
//         commitments: &[Self::Commitment],
//         points: &[Self::Point],
//         batch_proof: &Self::BatchProof,
//         transcript: &mut IOPTranscript<E::ScalarField>,
//     ) -> Result<bool, PCSError> {
//         unimplemented!();
//     }
// }
}

fn open_internal<E: Pairing<ScalarField = ark_ff::Fp<MontBackend<FrConfig, 4>, 4>>>(
    pp: &UniversalParams<Bls12_381>,
    f_hat_coeffs: &[F],
    f_poly: &DenseMultilinearExtension<F>,
    miu: u32,
    z: Vec<F>,
) -> Result<(SamaritanProof,F), PCSError> {
    let open_timer = start_timer!(|| format!("open mle with {} variable", miu));

    let v = f_poly
        .evaluate(&z)
        .ok_or_else(|| PCSError::InvalidParameters("Failed to evaluate f_poly at z".to_string()))?;
    let n = 1 << miu;
    let l = 1 << miu.ilog2();
    let m = n / l;
    let k = log2(m) as usize;
    let empty_randomness = Randomness::<Fr, DensePolynomial<Fr>>::empty();

    let mut commitments = Vec::new();
    let mut evaluations = Vec::new();
    let mut proofs = Vec::new();
    // 第二步
    // 先计算g_hat
    let g_hat = generate_ghat(&f_hat_coeffs, miu);
    // for (i, g) in g_hat.iter().enumerate() {
    //     // println!("g_hat{}: {:?}", i + 1, g.coeffs);
    // }
    // 再计算Q(X,Y)
    let q_poly = compute_q(&g_hat, l); /////////
    println!("OK222");
    // 第三步
    // 先分出z_x，z_y
    let z_x = &z[z.len() - k..];
    let z_y = &z[..miu as usize - k];
    // println!("z{:?}",z);
    // println!("z_y{:?}",z_y);
    // println!("z_x{:?}", z_x);
    // 再计算v_i
    let mut v_vec: Vec<F> = Vec::with_capacity(l);
    for i in 1..=l {
        let g_tilde = compute_gtilde(f_poly, miu, i);
        // println!("g_tilde{:?}", g_tilde);
        let v_i = g_tilde.evaluate(&z_x);
        v_vec.push(v_i.unwrap());
        // println!("v_{} = tilde_g_{}({:?}) = {:?}", i, i, z_x, v_i);
    }
    println!("OK333");

    // 第四步
    // 先计算v_hat
    let v_hat = DensePolynomial::from_coefficients_vec(v_vec.clone());
    // println!("OK444111");
    // 再计算ψ_hat
    let psi_hat = compute_psihat(&z_y);
    // println!("OK444222");
    // println!("psi_hat(X) = {:?}", psi_hat.coeffs);
    // let psi_hat_z = compute_psihat(&z);
    // println!("v_psi_z(X) = {:?}", psi_hat_z.coeffs);
    let v_psi = polynomial_mul(&v_hat, &psi_hat);
    // println!("OK444333");
    // // let v_psi = &v_hat * &psi_hat;
    // let f_hat =
    // DensePolynomial::from_coefficients_vec(f_hat_coeffs.to_vec().clone());
    // let test = polynomial_mul(&psi_hat_z , &f_hat);
    // println!("OK444444");
    // let test = &psi_hat_z * &f_hat;
    let mut a_coeffs = vec![F::zero(); v_psi.degree() - l + 1];
    let mut b_coeffs = vec![F::zero(); l - 1];
    // println!("START111");
    for i in l..=v_psi.degree() {
        a_coeffs[i - l] = v_psi.coeffs[i];
    }

    if (v == Fr::from(v_psi.coeffs[l - 1].into_bigint())) {
        println!("YES111");
    } else {
        println!("NO111")
    }
    for i in 0..l - 1 {
        b_coeffs[i] = v_psi.coeffs[i];
    }

    // if (v == Fr::from(test.coeffs[n - 1].into_bigint())) {
    //     println!("YES333");
    // } else {
    //     println!("NO333")
    // }

    let a_hat = DensePolynomial::from_coefficients_vec(a_coeffs);
    let b_hat = DensePolynomial::from_coefficients_vec(b_coeffs);
    // let test = v_psi.coeffs[l - 1].into_bigint();
    // println!("v_psi(X) = {:?}", v_psi.coeffs);
    // println!("a_hat(X) = {:?}", a_hat.coeffs);
    // println!("test = {:?}",test.coeffs);
    // println!("v = {:?}", v);
    // // println!("v_psi.coeffs(l-1)={:?}", test);
    // println!("b_hat(X) = {:?}", b_hat.coeffs);

    // 第五步
    let (cm_v, _) = commit(pp, &v_hat);
    let (cm_a, _) = commit(pp, &a_hat);
    commitments.push(cm_v);
    commitments.push(cm_a);

    let mut transcript = IOPTranscript::<E::ScalarField>::new(b"MyKZGPCS");

    let mut buf_v = Vec::new();
    cm_v.serialize_compressed(&mut buf_v)?; // 序列化为字节
    transcript.append_message(b"commitment_v", &buf_v)?;

    let mut buf_a = Vec::new();
    cm_a.serialize_compressed(&mut buf_a)?; // 序列化为字节
    transcript.append_message(b"commitment_a", &buf_a)?;

    let gamma: E::ScalarField = transcript.get_and_append_challenge(b"challenge_gamma")?;

    // 第七步
    // 计算v(γ)
    let (v_gamma, proof_vgamma) = kzg_prove(&pp, &v_hat, gamma)?;
    proofs.push(proof_vgamma);

    let p_hat = compute_phat(q_poly.clone(), gamma);
    // println!("p_hat(X) = Q(gamma, X) = {:?}", p_hat);

    // 计算r_hat
    let r_poly = compute_r(q_poly, gamma);
    let r_hat = compute_r_hat(r_poly, m);

    // 第八步

    let psi_hat_y = compute_psihat(z_x);
    let p_psi = &p_hat * &psi_hat_y;
    // 计算h_hat,u_hat
    let mut h_coeffs = vec![F::zero(); p_psi.degree() - m + 1];
    let mut u_coeffs = vec![F::zero(); m - 1];

    for i in m..=p_psi.degree() {
        h_coeffs[i - m] = p_psi.coeffs[i];
    }
    if (v_gamma == Fr::from(p_psi.coeffs[m - 1].into_bigint())) {
        println!("YES222");
    } else {
        println!("NO222")
    }
    for i in 0..m - 1 {
        u_coeffs[i] = p_psi.coeffs[i];
    }

    let h_hat = DensePolynomial::from_coefficients_vec(h_coeffs);
    let u_hat = DensePolynomial::from_coefficients_vec(u_coeffs);

    // println!("p_psi(X) = {:?}", p_psi.coeffs);
    // println!("h_hat(X) = {:?}", h_hat.coeffs);
    // println!("v_gamma = {:?}", v_gamma);
    // println!(
    //     "p_psi.coeffs(m-1)={}",
    //     Fr::from(p_psi.coeffs[m - 1].into_bigint())
    // );
    // println!("u_hat(X) = {:?}", u_hat.coeffs);

    // 第九步
    let (cm_p, _) = commit(pp, &p_hat);
    let (cm_r, _) = commit(pp, &r_hat);
    let (cm_h, _) = commit(pp, &h_hat);
    commitments.push(cm_p);
    commitments.push(cm_r);
    commitments.push(cm_h);

    let mut buf_p = Vec::new();
    cm_p.serialize_compressed(&mut buf_p)?; // 序列化为字节
    transcript.append_message(b"commitment_p", &buf_p)?;
    let mut buf_r = Vec::new();
    cm_r.serialize_compressed(&mut buf_r)?; // 序列化为字节
    transcript.append_message(b"commitment_r", &buf_r)?;
    let mut buf_h = Vec::new();
    cm_h.serialize_compressed(&mut buf_h)?; // 序列化为字节
    transcript.append_message(b"commitment_h", &buf_h)?;
    let beta: E::ScalarField = transcript.get_and_append_challenge(b"challenge_beta")?;
    // 第十一步
    // 先分别取逆
    // 构造 t(X)
    let t_poly = compute_t(&p_hat, &u_hat, &b_hat, beta, m as u64, l as u64);
    // println!("t(X) = {:?}", t_poly.coeffs);

    let (cm_t, _) = commit(pp, &t_poly);
    commitments.push(cm_t);

    let mut buf_t = Vec::new();
    cm_t.serialize_compressed(&mut buf_t)?; // 序列化为字节
    transcript.append_message(b"commitment_t", &buf_t)?;

    let delta: E::ScalarField = transcript.get_and_append_challenge(b"challenge_delta")?;

    // println!("delta: {:?}", delta);

    let delta_inv = delta.inverse().unwrap();

    let f_hat = DensePolynomial::from_coefficients_vec(f_hat_coeffs.to_vec());
    let (f_delta, proof_fdelta) = kzg_prove(&pp, &f_hat, delta)?;
    proofs.push(proof_fdelta);

    let (p_delta, proof_pdelta) = kzg_prove(&pp, &p_hat, delta)?;
    proofs.push(proof_pdelta);

    let (h_delta, proof_hdelta) = kzg_prove(&pp, &h_hat, delta)?;
    proofs.push(proof_hdelta);

    let (v_delta, proof_vdelta) = kzg_prove(&pp, &v_hat, delta)?;
    proofs.push(proof_vdelta);

    let (a_delta, proof_adelta) = kzg_prove(&pp, &a_hat, delta)?;
    proofs.push(proof_adelta);

    let b_delta = b_hat.evaluate(&delta);
    println!("b_delta = {:?}", b_delta);

    let (t_delta_inv, proof_tdelta_inv) = kzg_prove(&pp, &t_poly, delta_inv)?;
    proofs.push(proof_tdelta_inv);
    // println!("t1(delta^{{-1}}) = {:?}", t_delta_inv);
    // let t_delta_inv = delta_m1 * p_delta + beta * delta_m2 * u_delta + beta*beta
    // * delta_l2 * b_delta; println!("t(delta^{{-1}}) = {:?}", t_delta_inv);

    let eval_slice: Vec<F> = vec![
        delta,
        t_delta_inv,
        f_delta,
        p_delta,
        h_delta,
        v_delta,
        a_delta,
        v,
        v_gamma,
        beta,
        F::from(m as u64),
        F::from(l as u64),
    ];
    evaluations.extend_from_slice(&eval_slice);
    let evaluation = evaluations[0];

    let mut proofs_byte = Vec::new();
    proofs.serialize_compressed(&mut proofs_byte)?;

    end_timer!(open_timer);
    Ok((SamaritanProof {
        commitments,
        evaluations,
        batch_proof: Some(proofs_byte),
    },
    evaluation))
}

fn verify_internal<E: Pairing<ScalarField = ark_ff::Fp<MontBackend<FrConfig, 4>, 4>>>(
    commitment:  &Commitment<Bls12_381>,
    verifier_param: &UniversalParams<Bls12_381>,
    z: Vec<F>,
    proof: &SamaritanProof,
) -> Result<bool, PCSError> {
    let verify_timer = start_timer!(|| "verify");
    let cm_v = proof.commitments[0];
    let cm_a = proof.commitments[1];
    let cm_p = proof.commitments[2];
    let cm_r = proof.commitments[3];
    let cm_h = proof.commitments[4];
    let cm_t = proof.commitments[5];

    //恢复gamma
    let mut transcript = IOPTranscript::<E::ScalarField>::new(b"MyKZGPCS");
    let mut buf_v = Vec::new();
    cm_v.serialize_compressed(&mut buf_v)?; // 序列化为字节
    transcript.append_message(b"commitment_v", &buf_v)?;

    let mut buf_a = Vec::new();
    cm_a.serialize_compressed(&mut buf_a)?; // 序列化为字节
    transcript.append_message(b"commitment_a", &buf_a)?;

    let gamma: E::ScalarField = transcript.get_and_append_challenge(b"challenge_gamma")?;

    let mut buf_p = Vec::new();
    cm_p.serialize_compressed(&mut buf_p)?; // 序列化为字节
    transcript.append_message(b"commitment_p", &buf_p)?;
    let mut buf_r = Vec::new();
    cm_r.serialize_compressed(&mut buf_r)?; // 序列化为字节
    transcript.append_message(b"commitment_r", &buf_r)?;
    let mut buf_h = Vec::new();
    cm_h.serialize_compressed(&mut buf_h)?; // 序列化为字节
    transcript.append_message(b"commitment_h", &buf_h)?;
    let beta: E::ScalarField = transcript.get_and_append_challenge(b"challenge_beta")?;

    let mut buf_t = Vec::new();
    cm_t.serialize_compressed(&mut buf_t)?; // 序列化为字节
    transcript.append_message(b"commitment_t", &buf_t)?;

    let delta: E::ScalarField = transcript.get_and_append_challenge(b"challenge_delta")?;

    let t_delta_inv = proof.evaluations[1];
    let f_delta = proof.evaluations[2];
    let p_delta = proof.evaluations[3];
    let h_delta = proof.evaluations[4];
    let v_delta = proof.evaluations[5];
    let a_delta = proof.evaluations[6];
    let v = proof.evaluations[7];
    let v_gamma = proof.evaluations[8];
    let beta = proof.evaluations[9];
    let m_f = proof.evaluations[10];
    let l_f = proof.evaluations[11];

    let m: usize = m_f.into_bigint().as_ref()[0] as usize;
    let l: usize = l_f.into_bigint().as_ref()[0] as usize;

    let delta_inv = delta
        .inverse()
        .ok_or_else(|| PCSError::InvalidParameters("Delta inverse failed".to_string()))?;
    let delta_m1 = delta_inv.pow(&[(m - 1) as u64]);
    let delta_m2 = delta_inv.pow(&[(m - 2) as u64]);
    let delta_l2 = delta_inv.pow(&[(l - 2) as u64]);

    let batch_commitments = vec![
        cm_v,          
        *commitment,   
        cm_p,        
        cm_h,          
        cm_v,          
        cm_a,          
        cm_t,         
    ];

    let batch_points = vec![
        gamma,      
        delta,     
        delta,      
        delta,      
        delta,      
        delta,      
        delta_inv,  
    ];

    let batch_values = vec![
        v_gamma,    
        f_delta,     
        p_delta,     
        h_delta,     
        v_delta,     
        a_delta,     
        t_delta_inv, 
    ];

    let batch_proof_bytes = proof.batch_proof.as_ref()
        .ok_or_else(|| PCSError::InvalidProof("Missing batch proof".to_string()))?;
    let kzg_proofs: Vec<Proof<Bls12_381>> = CanonicalDeserialize::deserialize_compressed(&mut &batch_proof_bytes[..])
        .map_err(|e| PCSError::InvalidProof(format!("Failed to deserialize batch proof: {:?}", e)))?;

   
        let vk = VerifierKey {
            g: verifier_param.powers_of_g.get(0)
                .ok_or_else(|| PCSError::InvalidParameters("powers_of_g is empty".to_string()))?.clone(),
            gamma_g: verifier_param.powers_of_gamma_g.get(&0)
                .ok_or_else(|| PCSError::InvalidParameters("No gamma_g at index 0 in powers_of_gamma_g".to_string()))?.clone(),
            h: verifier_param.h,
            beta_h: verifier_param.beta_h,
            prepared_h: verifier_param.prepared_h.clone(),
            prepared_beta_h: verifier_param.prepared_beta_h.clone(),
        };

        let mut rng = ChaCha8Rng::from_seed([0u8; 32]); 

        let batch_result = KZG10::<Bls12_381, Poly>::batch_check(
            &vk,
            &batch_commitments,
            &batch_points,
            &batch_values,
            &kzg_proofs,
            &mut rng, 
        ).map_err(|e| PCSError::InvalidProof(format!("KZG batch check failed: {:?}", e)))?;

    let result = batch_result;
    println!("KZG 批量验证: {}", if result { "成功" } else { "失败" });

    let mu = z.len();
    let k = log2(m) as usize;
    let z_y = &z[..mu - k];
    let z_x = &z[mu - k..];
    let psi_hat_y = compute_psihat(z_x);
    let psi_delta_y = psi_hat_y.evaluate(&delta);
    let delta_m = delta.pow(&[m as u64]);
    let delta_m_1 = delta.pow(&[(m - 1) as u64]);
    let u_delta = p_delta * psi_delta_y - delta_m * h_delta - v_gamma * delta_m_1;
    // println!("u_verify{:?}", u_delta);
    let psi_hat_x = compute_psihat(z_y);
    let psi_delta_x = psi_hat_x.evaluate(&delta);
    let delta_l = delta.pow(&[l as u64]);
    let delta_l_1 = delta.pow(&[(l - 1) as u64]);
    let b_delta = v_delta * psi_delta_x - delta_l * a_delta - v * delta_l_1;
    // println!("b_verify{:?}", b_delta);
    let rhs = delta_m1 * p_delta + beta * delta_m2 * u_delta + beta * beta * delta_l2 * b_delta;
    println!("rhs = {}", rhs);
    println!("t_delta_inv = {}", t_delta_inv);
    let mut res = false;

    if t_delta_inv != rhs {
        println!("验证失败");
    } else {
        res = true;
        println!("验证成功");
    }
    end_timer!(verify_timer);
    Ok(res)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pcs::multilinear_kzg::{MultilinearKzgPCS, MultilinearKzgProof};
    use ark_bls12_381::{Bls12_381, Fr, Fr as Bls12_381Fr};
    use ark_poly::{evaluations, univariate::DensePolynomial, DenseMultilinearExtension, MultilinearExtension};
    use ark_std::{sync::Arc, test_rng, vec::Vec, UniformRand};
    use env_logger;

    #[test]
    fn test_method() {
        env_logger::init();
        let mut lambda = 128;
        let miu = 20 as usize;
        let mut rng = test_rng();
        let pp =
            SamaritanPCS::<Bls12_381>::gen_srs_for_testing(&mut rng, miu).expect("生成 SRS 失败");

        let evaluations: Vec<Fr> = (1..=1 << miu).map(|i| Fr::from(i as u64)).collect();
        // let poly =
        //     DenseMultilinearExtension::from_evaluations_vec(miu as usize, evaluations.clone());

        let f_hat_coeffs = compute_f_hat(&evaluations, miu);
        let f_hat = DensePolynomial::from_coefficients_vec(f_hat_coeffs.clone());

        let commitment = SamaritanPCS::<Bls12_381>::commit(&pp, &f_hat).expect("承诺失败");

        let z: Vec<F> = (0..miu).map(|_| F::rand(&mut rng)).collect();
        // let mut z: Vec<F> = vec![F::from(1), F::from(0), F::from(1), F::from(0)];
        let (proof,evaluation) = SamaritanPCS::<Bls12_381>::open(&pp, &f_hat,&z).expect("打开承诺失败");
        // let v = poly.evaluate(&z);
        // println!("v={:?}",v);
        let is_valid =
            SamaritanPCS::<Bls12_381>::verify(&pp, &commitment, &z, &proof.evaluations[0], &proof)
                .expect("验证失败");

        assert!(is_valid, "证明验证未通过");
        println!("承诺、打开和验证测试成功！");
    }

    #[test]
    fn test_multilinear_kzg_timing() {
        type E = Bls12_381;
        type F = Bls12_381Fr;
        // env_logger::init();
        let mut rng = test_rng();
        let num_vars = 20; // 变量数量

        let params = MultilinearKzgPCS::<E>::gen_srs_for_testing(&mut rng, num_vars)
            .expect("MultilinearKzg SRS 生成失败");

        let (prover_param, verifier_param) =
            MultilinearKzgPCS::<E>::trim(&params, None, Some(num_vars)).expect("参数修剪失败");

        let evaluations: Vec<F> = (0..(1 << num_vars)).map(|_| F::rand(&mut rng)).collect();
        let poly = Arc::new(DenseMultilinearExtension::from_evaluations_vec(
            num_vars,
            evaluations,
        ));

        let z: Vec<F> = (0..num_vars).map(|_| F::rand(&mut rng)).collect();
        let eval = poly.evaluate(&z).unwrap();

        let commit_timer = start_timer!(|| "MultilinearKzgPCS commit");
        let commitment=
            MultilinearKzgPCS::<E>::commit(&prover_param, &poly).expect("MultilinearKzg 承诺失败");
        end_timer!(commit_timer);

        let open_timer = start_timer!(|| "MultilinearKzgPCS open");
        let (proof,evaluation) = MultilinearKzgPCS::<E>::open(&prover_param, &poly, &z)
            .expect("MultilinearKzg 打开承诺失败");
        end_timer!(open_timer);

        let verify_timer = start_timer!(|| "MultilinearKzgPCS verify");
        let is_valid =
            MultilinearKzgPCS::<E>::verify(&verifier_param, &commitment, &z, &eval, &proof)
                .expect("MultilinearKzg 验证失败");
        end_timer!(verify_timer);

        assert!(is_valid, "MultilinearKzg 证明验证未通过");
        println!("MultilinearKzgPCS 承诺、打开和验证测试成功！");
    }
}
