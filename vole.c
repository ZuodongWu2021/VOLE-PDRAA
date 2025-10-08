/*
 *  SPDX-License-Identifier: MIT
 */

#if defined(HAVE_CONFIG_H)
#include <config.h>
#endif

#include "vole.h"
#include "aes.h"
#include "utils.h"
#include "random_oracle.h"
#include "build/faest_128f.h" 
#include <stdbool.h>
#include <string.h>
#include "randomness.h" 

static const uint32_t TWEAK_OFFSET = UINT32_C(0x80000000); // 2^31

#if !defined(FAEST_TESTS)
static
#endif
    unsigned int
    convert_to_vole(const uint8_t* iv, const uint8_t* sd, bool sd0_bot, unsigned int i,
                    unsigned int outlen, uint8_t* u, uint8_t* v, const faest_paramset_t* params) {
  const unsigned int lambda        = params->lambda;
  const unsigned int tau_1         = params->tau1;
  const unsigned int k             = params->k;
  const unsigned int num_instances = bavc_max_node_index(i, tau_1, k);
  const unsigned int lambda_bytes  = lambda / 8;
  const unsigned int depth         = bavc_max_node_depth(i, tau_1, k);

  // (depth + 1) x num_instances array of outlen; but we only need two rows at a time
  uint8_t* r = calloc(2 * num_instances, outlen);

#define R(row, column) (r + (((row) % 2) * num_instances + (column)) * outlen)
#define V(idx) (v + (idx) * outlen)

  uint32_t tweak = i ^ TWEAK_OFFSET;

  // Step: 2
  if (!sd0_bot) {
    prg(sd, iv, tweak, R(0, 0), lambda, outlen);
  }

  // Step: 3..4
  for (unsigned int j = 1; j < num_instances; ++j) {
    prg(sd + lambda_bytes * j, iv, tweak, R(0, j), lambda, outlen);
  }

  // Step: 5..9
  memset(v, 0, depth * outlen);
  for (unsigned int j = 0; j < depth; j++) {
    unsigned int depthloop = num_instances >> (j + 1);
    for (unsigned int idx = 0; idx < depthloop; idx++) {
      xor_u8_array(V(j), R(j, 2 * idx + 1), V(j), outlen);
      xor_u8_array(R(j, 2 * idx), R(j, 2 * idx + 1), R(j + 1, idx), outlen);
    }
  }
  // Step: 10
  if (!sd0_bot && u != NULL) {
    memcpy(u, R(depth, 0), outlen);
  }
  free(r);
  return depth;
}

void vole_commit(const uint8_t* rootKey, const uint8_t* iv, unsigned int ellhat,
                 const faest_paramset_t* params, bavc_t* bavc, uint8_t* c, uint8_t* u,
                 uint8_t** v) {
  const unsigned int lambda       = params->lambda;
  const unsigned int lambda_bytes = lambda / 8;
  const unsigned int ellhat_bytes = (ellhat + 7) / 8;
  const unsigned int tau          = params->tau;
  const unsigned int tau_1        = params->tau1;
  const unsigned int k            = params->k;

  bavc_commit(bavc, rootKey, iv, params);

  uint8_t* ui = malloc(tau * ellhat_bytes);
  assert(ui);

  unsigned int v_idx = 0;
  uint8_t* sd_i      = bavc->sd;
  for (unsigned int i = 0; i < tau; ++i) {
    // Step 6
    v_idx +=
        convert_to_vole(iv, sd_i, false, i, ellhat_bytes, ui + i * ellhat_bytes, v[v_idx], params);
    sd_i += lambda_bytes * bavc_max_node_index(i, tau_1, k);
  }

  // ensure 0-padding up to lambda
  for (; v_idx != lambda; ++v_idx) {
    memset(v[v_idx], 0, ellhat_bytes);
  }

  // Step 9
  memcpy(u, ui, ellhat_bytes);
  for (unsigned int i = 1; i < tau; i++) {
    // Step 11
    xor_u8_array(u, ui + i * ellhat_bytes, c + (i - 1) * ellhat_bytes, ellhat_bytes);
  }
  free(ui);
}

bool vole_reconstruct(uint8_t* com, uint8_t** q, const uint8_t* iv, const uint8_t* chall_3,
                      const uint8_t* decom_i, const uint8_t* c, unsigned int ellhat,
                      const faest_paramset_t* params) {
  const unsigned int lambda       = params->lambda;
  const unsigned int lambda_bytes = lambda / 8;
  const unsigned int ellhat_bytes = (ellhat + 7) / 8;
  const unsigned int tau          = params->tau;
  const unsigned int tau1         = params->tau1;
  const unsigned int L            = params->L;
  const unsigned int k            = params->k;

  uint16_t i_delta[MAX_TAU];
  if (!decode_all_chall_3(i_delta, chall_3, params)) {
    return false;
  }

  bavc_rec_t bavc_rec;
  bavc_rec.h = com;
  bavc_rec.s = malloc((L - tau) * lambda_bytes);
  assert(bavc_rec.s);

  if (!bavc_reconstruct(&bavc_rec, decom_i, i_delta, iv, params)) {
    free(bavc_rec.s);
    return false;
  }

  uint8_t* sd   = malloc((1 << k) * lambda_bytes);
  uint8_t* qtmp = malloc(MAX_DEPTH * ellhat_bytes);
  assert(sd);
  assert(qtmp);

  // Step: 1
  unsigned int q_idx = 0;
  uint8_t* sd_i      = bavc_rec.s;
  for (unsigned int i = 0; i < tau; i++) {
    // Step: 2
    const unsigned int Ni = bavc_max_node_index(i, tau1, k);

    // Step: 6
    for (unsigned int j = 0; j < Ni; j++) {
      if (j < i_delta[i]) {
        memcpy(sd + (j ^ i_delta[i]) * lambda_bytes, sd_i + lambda_bytes * j, lambda_bytes);
      } else if (j > i_delta[i]) {
        memcpy(sd + (j ^ i_delta[i]) * lambda_bytes, sd_i + lambda_bytes * (j - 1), lambda_bytes);
      }
    }

    // Step: 7..8
    const unsigned int ki = convert_to_vole(iv, sd, true, i, ellhat_bytes, NULL, qtmp, params);

    // Step 11
    if (i == 0) {
      // Step 8
      memcpy(q[q_idx], qtmp, ellhat_bytes * ki);
      q_idx += ki;
    } else {
      // Step 14
      for (unsigned int d = 0; d < ki; ++d, ++q_idx) {
        masked_xor_u8_array(qtmp + d * ellhat_bytes, c + (i - 1) * ellhat_bytes, q[q_idx],
                            (i_delta[i] >> d) & 1, ellhat_bytes);
      }
    }
    sd_i += lambda_bytes * (Ni - 1);
  }

  // ensure 0-padding up to lambda
  for (; q_idx != lambda; ++q_idx) {
    memset(q[q_idx], 0, ellhat_bytes);
  }

  free(qtmp);
  free(sd);
  free(bavc_rec.s);
  return true;
}



/*

// 将测试逻辑放在一个自定义函数中，不直接写在 main 里
static int run_faest_128f_test(void) {

    int ret;

    // 分配公私钥缓冲，大小由宏定义给出
    uint8_t pk[FAEST_128F_PUBLIC_KEY_SIZE];
   
    uint8_t sk[FAEST_128F_PRIVATE_KEY_SIZE];
   

    // 1. 密钥生成
   ret = faest_128f_keygen(
        pk ,    // 输出：公钥及其长度
        sk    // 输出：私钥及其长度
    );

    if (ret != 0) {
        fprintf(stderr, "faest_128f_keygen failed: %d\n", ret);
        return EXIT_FAILURE;
    }

    // 可选：对生成的密钥进行验证
    ret = faest_128f_validate_keypair(pk, sk);
    if (ret != 0) {
        fprintf(stderr, "faest_128f_validate_keypair failed: %d\n", ret);
        return EXIT_FAILURE;
    }


    // 2. 构造待签名消息（示例用固定字符串，也可以改成随机或输入数据）
    const uint8_t message[] = "Hello FAEST-128f!";
    size_t message_len = sizeof(message) - 1;

    // 准备签名输出缓冲，FAEST_128F_SIGNATURE_SIZE 定义了签名的最大可能长度
    uint8_t signature[FAEST_128F_SIGNATURE_SIZE];
    size_t signature_len = FAEST_128F_SIGNATURE_SIZE;

    // 3. 签名
    ret = faest_128f_sign(sk, message, message_len, signature, &signature_len);
    if (ret != 0) {
        fprintf(stderr, "faest_128f_sign failed: %d\n", ret);
        return EXIT_FAILURE;
    }
    // signature_len 现在持有实际签名长度

    // 4. 验签
    ret = faest_128f_verify(pk, message, message_len, signature, signature_len);
    if (ret != 0) {
        fprintf(stderr, "faest_128f_verify failed: %d\n", ret);
        return EXIT_FAILURE;
    }

    // 如果到达这里，说明签名和验签均成功
    printf("Sign/Verify test passed\n");
    return EXIT_SUCCESS;
}

 void run_vole_simple_test() {
    // 获取 FAEST-128f 参数集
    const faest_paramset_t *params = faest_get_paramset(FAEST_128F);
    unsigned int lambda = params->lambda;
    unsigned int tau = params->tau;
    unsigned int ellhat = params->l + params->lambda * 3 + UNIVERSAL_HASH_B_BITS;
    unsigned int ellhat_bytes = (ellhat + 7) / 8;

    // 准备随机根密钥和 IV（这里以示例值填充）
    uint8_t rootKey[32];
    for (int i = 0; i < 32; i++) rootKey[i] = (uint8_t)i;
    uint8_t iv[IV_SIZE] = {0};

    // 分配 BAVC 结构和输出缓冲区
    bavc_t vecCom;
    uint8_t *c = malloc((tau - 1) * ellhat_bytes);
    uint8_t *u = malloc(ellhat_bytes);
    uint8_t **v = malloc(lambda * sizeof(uint8_t*));
    for (unsigned int i = 0; i < lambda; i++) {
        v[i] = malloc(ellhat_bytes);
    }

    // 调用 VOLE 承诺生成器
    vole_commit(rootKey, iv, ellhat, params, &vecCom, c, u, v);

    // 提取第 0 位进行测试
    uint8_t u0 = u[0] & 1;
    uint8_t V = v[0][0] & 1;

    // 生成误差 Δ（一个随机比特）
    uint8_t delta;
    rand_bytes(&delta, 1);
    delta &= 1;

    // 在 GF(2) 域中计算 Q = V + u0*Δ（即异或运算）
    uint8_t Q = V ^ (u0 & delta);

    // 输出调试信息
    printf("VOLE 测试: u0=%u, Δ=%u, V=%u, Q=%u\n", u0, delta, V, Q);

    // 释放内存
    free(c);
    free(u);
    for (unsigned int i = 0; i < lambda; i++) {
        free(v[i]);
    }
    free(v);
    free(vecCom.h);
    free(vecCom.k);
    free(vecCom.com);
    free(vecCom.sd);
}


int main(int argc, char *argv[]) {
    (void)argc; (void)argv;
     run_vole_simple_test();  // 附加的 VOLE 测试
     run_faest_128f_test();

    return  0;
     
}*/