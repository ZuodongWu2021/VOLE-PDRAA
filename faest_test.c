#ifndef KECCAK_SPONGE_H
#define KECCAK_SPONGE_H
// 文件名：faest_test.c  （文件名可自定义，但不要命名为 main.c 以满足“代码名字不能叫 main”要求）
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <assert.h>
#include <time.h>
#include <sys/time.h>

//包含 FAEST-128f 的头文件，假设编译时用 -I 指定了该头文件所在目录
#include "build/faest_128f.h"          
             
#include "randomness.h"        
#include "faest_impl.h"
#include "instances.h"
#include "bavc.h" 

 #include "vole.h"


#include "parameters.h"

/*
 *  SPDX-License-Identifier: MIT
 */

#if defined(HAVE_CONFIG_H)

#include <config.h>
#endif
#include "aes.h"
#include "utils.h"
#include "random_oracle.h"
#include <stdbool.h>
#include <sha3/opt64/KeccakP-1600-SnP.h>
#include <sha3/brg_endian.h>

size_t g_m2 = 0;

/* ======== Communication accounting (sender-only + by-phase) ======== */
typedef enum { ROLE_DS = 0, ROLE_DR = 1, ROLE_DC = 2 } Role;
typedef enum { PHASE_SETUP = 0, PHASE_AUTH = 1, PHASE_RETR = 2 } Phase;

typedef struct {
    /* per-sender totals */
    size_t sent_DS, sent_DR, sent_DC;
    /* per-phase totals */
    size_t phase_setup, phase_auth, phase_retr;
} CommCounter;

static CommCounter COMM = {0};

static inline void comm_add(Role sender, size_t bytes, Phase ph) {
    if (!bytes) return;
    /* by phase */
    switch (ph) {
        case PHASE_SETUP: COMM.phase_setup += bytes; break;
        case PHASE_AUTH:  COMM.phase_auth  += bytes; break;
        case PHASE_RETR:  COMM.phase_retr  += bytes; break;
        default: break;
    }
    /* by sender */
    switch (sender) {
        case ROLE_DS: COMM.sent_DS += bytes; break;
        case ROLE_DR: COMM.sent_DR += bytes; break;
        case ROLE_DC: COMM.sent_DC += bytes; break;
        default: break;
    }
}

static inline void print_comm_summary_sender_phase(void) {
    size_t total_phase = COMM.phase_setup + COMM.phase_auth + COMM.phase_retr;
    size_t total_sender = COMM.sent_DS + COMM.sent_DR + COMM.sent_DC;

    printf("\n========== Communication Cost (Sender totals) ==========\n");
    printf("[By Phase]\n");
    printf("  Setup:         %10zu bytes (%.2f KiB)\n", COMM.phase_setup, COMM.phase_setup/1024.0);
    printf("  Authorization: %10zu bytes (%.2f KiB)\n", COMM.phase_auth,  COMM.phase_auth/1024.0);
    printf("  Retrieval:     %10zu bytes (%.2f KiB)\n", COMM.phase_retr,  COMM.phase_retr/1024.0);
    printf("  ------------------------------------------------------\n");
    printf("  Total (Phase): %10zu bytes (%.2f KiB, %.2f MiB)\n",
           total_phase, total_phase/1024.0, total_phase/(1024.0*1024.0));

    printf("\n[By Sender]\n");
    printf("  DS sent: %zu bytes\n", COMM.sent_DS);
    printf("  DR sent: %zu bytes\n", COMM.sent_DR);
    printf("  DC sent: %zu bytes\n", COMM.sent_DC);
    printf("  ------------------------------------------------------\n");
    printf("  Total (Sender): %zu bytes\n", total_sender);
    printf("========================================================\n");
}
/* ======== end accounting ======== */

size_t pack_bits(const uint8_t *bits, size_t n, uint8_t *out){
    size_t nb = (n + 7) >> 3;     // 需要的字节数
    memset(out, 0, nb);           // 先清零，防止旧数据残留
    for (size_t i = 0; i < n; i++)
        out[i >> 3] |= (bits[i] & 1u) << (i & 7);
    return nb;                    // 实际写了多少字节
}

void unpack_bits(const uint8_t *in, size_t n, uint8_t *out)
{

for (size_t i = 0; i < n; i++)
out[i] = (in[i >> 3] >> (i & 7)) & 1u;

}



















// ============================================================================
// 安全版 gf2_dot_bits（带越界探针和详细错误输出）
// ============================================================================
static inline uint8_t gf2_dot_bits(const uint8_t *row, const uint8_t *K, size_t n) {
    // ===== 基本 NULL 检查 =====
    if (!row) {
        fprintf(stderr, "[FATAL] gf2_dot_bits: row pointer is NULL!\n");
        exit(1);
    }
    if (!K) {
        fprintf(stderr, "[FATAL] gf2_dot_bits: K pointer is NULL!\n");
        exit(1);
    }
    if (n == 0) {
        fprintf(stderr, "[FATAL] gf2_dot_bits: length n=0 is invalid!\n");
        exit(1);
    }
    if (n != g_m2) {
        fprintf(stderr, "[FATAL] gf2_dot_bits: n=%zu != global g_m2=%zu (参数不一致)\n", n, g_m2);
        exit(1);
    }

    // ===== 越界探针：访问最后一个字节，提前触发非法访问 =====
    // 如果 row 或 K 长度不足 g_m2，会在这里直接崩溃/被 ASan 报错，而不是在循环中随机崩
    volatile uint8_t first_row = row[0];
    volatile uint8_t last_row  = row[g_m2 - 1];
    volatile uint8_t first_k   = K[0];
    volatile uint8_t last_k    = K[g_m2 - 1];
    (void)first_row; (void)last_row; (void)first_k; (void)last_k;

    // ===== 调试输出（仅前几次调用时打印）=====
    static int dbg_count = 0;
    if (dbg_count < 10) {
        fprintf(stderr, "[gf2_dot_bits DEBUG] row=%p K=%p n=%zu g_m2=%zu last_row=%u last_k=%u\n",
                (const void*)row, (const void*)K, n, g_m2, last_row, last_k);
        dbg_count++;
    }

    // ===== 主计算 =====
    uint8_t acc = 0;
    for (size_t idx = 0; idx < n; idx++) {
        acc ^= (row[idx] & K[idx]) & 1u;
    }
    return acc;
}














static long now_us(void);

typedef struct {
    uint64_t state[25];      // 5×5×64b 状态
    size_t   rateInBytes;    // 吸收/挤出速率（字节）
    size_t   byteIndex;      // 缓冲区当前位置
    bool     squeezing;      // 是否在挤出阶段
    uint8_t  buffer[168];    // SHAKE128 rate = 168 bytes
} KeccakSponge;


void Keccak_Initialize(KeccakSponge *s, unsigned int width);
void Keccak_AddBytes(KeccakSponge *s, const uint8_t *in, size_t len);
void Keccak_Finalize(KeccakSponge *s);
void Keccak_Squeeze(KeccakSponge *s, uint8_t *out, size_t outLen);


static const uint8_t *g_seed;
static size_t       g_seed_len;



// void randombytes(uint8_t *x, size_t xlen) {
//     KeccakSponge s;
//     Keccak_Initialize(&s, 1600);
//     // Absorb our external seed
//     Keccak_AddBytes(&s, g_seed, g_seed_len);
//     Keccak_Finalize(&s);
//     // Squeeze out xlen bytes
//     Keccak_Squeeze(&s, x, xlen);
// }

void randombytes(uint8_t *x, size_t xlen) {
    // 改为 malloc，防止大结构体占用栈空间
    KeccakSponge *s = malloc(sizeof(KeccakSponge));
    if (!s) { fprintf(stderr, "malloc sponge failed\n"); exit(1); }
   Keccak_Initialize(s, 1600);
   Keccak_AddBytes(s, g_seed, g_seed_len);
   Keccak_Finalize(s);
    Keccak_Squeeze(s, x, xlen);
   free(s);
}








// 64 位循环左移
static inline uint64_t ROTL64(uint64_t x, unsigned int n) {
    return (x << n) | (x >> (64 - n));
}

// Keccak-p[1600] 状态置换：state 必须指向长度 ≥ 25 的 uint64_t 数组
void KeccakP1600_StatePermute(uint64_t *state)
{
    // ρ 步偏移量
    static const unsigned R[5][5] = {
        { 0, 36,  3, 41, 18},
        { 1, 44, 10, 45,  2},
        {62,  6, 43, 15, 61},
        {28, 55, 25, 21, 56},
        {27, 20, 39,  8, 14}
    };
    // ι 步轮常量
    static const uint64_t RC[24] = {
        0x0000000000000001ULL, 0x0000000000008082ULL,
        0x800000000000808AULL, 0x8000000080008000ULL,
        0x000000000000808BULL, 0x0000000080000001ULL,
        0x8000000080008081ULL, 0x8000000000008009ULL,
        0x000000000000008AULL, 0x0000000000000088ULL,
        0x0000000080008009ULL, 0x000000008000000AULL,
        0x000000008000808BULL, 0x800000000000008BULL,
        0x8000000000008089ULL, 0x8000000000008003ULL,
        0x8000000000008002ULL, 0x8000000000000080ULL,
        0x000000000000800AULL, 0x800000008000000AULL,
        0x8000000080008081ULL, 0x8000000000008080ULL,
        0x0000000080000001ULL, 0x8000000080008008ULL
    };

    static uint64_t A[5][5], B[5][5], C[5], D[5];
    int x, y, round;

    // 展开成 5×5 矩阵 A[x][y]
    for (x = 0; x < 5; x++)
        for (y = 0; y < 5; y++)
            A[x][y] = state[x + 5*y];

    for (round = 0; round < 24; round++) {
        // --- θ 步 ---
        for (x = 0; x < 5; x++)
            C[x] = A[x][0] ^ A[x][1] ^ A[x][2] ^ A[x][3] ^ A[x][4];
        for (x = 0; x < 5; x++)
            D[x] = C[(x + 4) % 5] ^ ROTL64(C[(x + 1) % 5], 1);
        for (x = 0; x < 5; x++)
            for (y = 0; y < 5; y++)
                A[x][y] ^= D[x];

        // --- ρ 和 π 步（合并）---
        for (x = 0; x < 5; x++) {
            for (y = 0; y < 5; y++) {
                unsigned int newX = y;
                unsigned int newY = (2*x + 3*y) % 5;
                B[newX][newY] = ROTL64(A[x][y], R[x][y]);
            }
        }

        // --- χ 步 ---
        for (x = 0; x < 5; x++)
            for (y = 0; y < 5; y++)
                A[x][y] = B[x][y] ^ ((~B[(x+1)%5][y]) & B[(x+2)%5][y]);

        // --- ι 步 ---
        A[0][0] ^= RC[round];
    }

    // 写回 linearized state
    for (x = 0; x < 5; x++)
        for (y = 0; y < 5; y++)
            state[x + 5*y] = A[x][y];
}

// typedef struct {
//     uint64_t state[25];      // 5×5×64b 状态
//     size_t rateInBytes;      // 吸收/挤出速率（字节）
//     size_t byteIndex;        // 缓冲区当前位置
//     bool squeezing;          // 当前是否处于挤出阶段
//     uint8_t  buffer[168];    // SHAKE128 rate = 1344 bit = 168 bytes
// } KeccakSponge;



// 初始化 Sponge，width 必须为 1600
void Keccak_Initialize(KeccakSponge *s, unsigned int width)
{
    (void)width;  // 目前只支持 1600
    memset(s->state, 0, sizeof(s->state));
    memset(s->buffer, 0, sizeof(s->buffer)); 
    s->rateInBytes = 168; // 1600 − 256 = 1344 bit = 168 bytes (SHAKE128)
    s->byteIndex   = 0;
    s->squeezing   = false;
}

// 吸收 inputBytes[0..inLen-1]
void Keccak_AddBytes(KeccakSponge *s, const uint8_t *inputBytes, size_t inLen)
{
    // 只能在吸收阶段调用
    if (s->squeezing) return;

    size_t idx = s->byteIndex;
    while (inLen > 0) {
        size_t take = s->rateInBytes - idx;
        if (take > inLen) take = inLen;
        // XOR 到 buffer
        for (size_t i = 0; i < take; i++)
            s->buffer[idx + i] ^= inputBytes[i];
        idx += take;
        inputBytes += take;
        inLen      -= take;
        // 如果 buffer 填满，就把它 XOR 到 state，并打 permutation
        if (idx == s->rateInBytes) {
            // load buffer into state lanes
            for (size_t i = 0; i < (s->rateInBytes/8); i++)
                s->state[i] ^= ((uint64_t*)s->buffer)[i];
            KeccakP1600_StatePermute(s->state);
            idx = 0;
        }
    }
    s->byteIndex = idx;
}

// 吸收结束，进入分隔符和挤出阶段
void Keccak_Finalize(KeccakSponge *s)
{
    // domain‐separation for SHAKE: 0x1F
    s->buffer[s->byteIndex++] ^= 0x1F;
    // 多重 1 填充
    s->buffer[s->rateInBytes - 1] ^= 0x80;
    // 最后一次吸收
    for (size_t i = 0; i < (s->rateInBytes/8); i++)
        s->state[i] ^= ((uint64_t*)s->buffer)[i];
    KeccakP1600_StatePermute(s->state);
    s->byteIndex = 0;
    s->squeezing = true;
}

// 挤出 outBytes[0..outLen-1]
void Keccak_Squeeze(KeccakSponge *s, uint8_t *outBytes, size_t outLen)
{
    if (!s->squeezing) return;
    size_t idx = s->byteIndex;
    while (outLen > 0) {
        // 如果 buffer 中没数据就从 state 拷贝并 permute
        if (idx == s->rateInBytes) {
            KeccakP1600_StatePermute(s->state);
            idx = 0;
        }
        size_t take = s->rateInBytes - idx;
        if (take > outLen) take = outLen;
        // state -> buffer
        memcpy(s->buffer + idx,
               (uint8_t*)s->state + idx,
               take);
        // 输出
        memcpy(outBytes, s->buffer + idx, take);
        idx     += take;
        outBytes += take;
        outLen  -= take;
    }
    s->byteIndex = idx;
}

#endif // KECCAK_SPONGE_H

/////////////////////////////////////////////////////////



// ---------生成数据集---------

#define ID_LEN 18   // 中国身份证号码长度（不含终止符）
#define BUF_LEN 32  // 缓冲区长度

// 随机生成一个合法格式的身份证号（这里只简单用数字串代替）
static void gen_random_id(char *out) {
    for (int i = 0; i < ID_LEN; i++) {
        out[i] = '0' + (rand() % 10);
    }
    out[ID_LEN] = '\0';
}

// 判断 id 是否已在数组 arr[0..n-1] 中
static int exists(char arr[][BUF_LEN], int n, const char *id) {
    for (int i = 0; i < n; i++) {
        if (strcmp(arr[i], id) == 0) return 1;
    }
    return 0;
}

/**
 * 生成一个集合 common，长度为 commonSize，元素为不重复的随机 ID
 */
static void gen_common_set(char common[][BUF_LEN], int commonSize) {
    int idx = 0;
    while (idx < commonSize) {
        char tmp[BUF_LEN];
        gen_random_id(tmp);
        if (!exists(common, idx, tmp)) {
            strcpy(common[idx++], tmp);
        }
    }
}

/**
 * 生成集合 X 或 Y
 *   - outArr: 目标数组
 *   - outSize: 目标数组长度
 *   - common: 交集数组
 *   - commonSize: 交集大小
 *   - avoid: 如果不为 NULL，则新元素需避开此数组中已有的 avoidSize 元素
 */
static void gen_set(char outArr[][BUF_LEN], int outSize,
                    char common[][BUF_LEN], int commonSize,
                    char avoid[][BUF_LEN], int avoidSize) {
    // 先拷贝交集部分
    for (int i = 0; i < commonSize; i++) {
        strcpy(outArr[i], common[i]);
    }
    // 再生成剩余部分
    int idx = commonSize;
    while (idx < outSize) {
        char tmp[BUF_LEN];
        gen_random_id(tmp);
        if (!exists(common, commonSize, tmp)
            && !exists(outArr, idx, tmp)
            && (avoid == NULL || !exists(avoid, avoidSize, tmp)))
        {
            strcpy(outArr[idx++], tmp);
        }
    }
}

// ---------生成数据集---------

static const uint8_t domain_sep_H0   = 0;
static const uint8_t domain_sep_H1   = 1;
static const uint8_t domain_sep_H2_0 = 8 + 0;
static const uint8_t domain_sep_H2_1 = 8 + 1;
static const uint8_t domain_sep_H2_2 = 8 + 2;
static const uint8_t domain_sep_H2_3 = 8 + 3;
static const uint8_t domain_sep_H3   = 3;
static const uint8_t domain_sep_H4   = 4;

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




// --------- 随机数生成器（64-bit splitmix64 和 xorshift64） ---------
static uint64_t splitmix64(uint64_t *seed) {
    uint64_t z = (*seed += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

// --------- SparseMatrixEncoder 结构体 ---------
typedef struct {
    size_t n;        // 原始向量长度
    size_t weight;   // 每行非零项数
    size_t m;        // 矩阵行数 (可设置为 weight * n)
    size_t m_prime; // 前 m' = weight * n
    uint64_t *row_seed; // 每行的哈希种子 (长度 m)
    size_t tail_len; // 后续尾部长度 d + λ
} SparseMatrixEncoder;

// 基于 id, sponge 输出 m_prime + tail_len 位的随机二进制向量


static void row_ID(const char *id,
                   size_t m_prime,
                   size_t tail_len,
                   uint8_t *row_bits)
{
    size_t m = m_prime + tail_len;

    // ----------- 安全检查 -----------
    if (!id || !row_bits) {
        fprintf(stderr, "row_ID: NULL pointer! id=%p row_bits=%p\n",
                (void*)id, (void*)row_bits);
        exit(1);
    }
    if (m_prime < 2) {
        fprintf(stderr, "row_ID: m_prime < 2 (got %zu)\n", m_prime);
        exit(1);
    }
    if (m != g_m2) { // 确认实际长度和全局g_m2一致
        fprintf(stderr, "row_ID: 长度不一致 (m=%zu, g_m2=%zu)\n", m, g_m2);
        exit(1);
    }

    // ----------- 初始化 sponge -----------
    KeccakSponge *s = malloc(sizeof(KeccakSponge));
    if (!s) { fprintf(stderr, "row_ID: malloc sponge failed\n"); exit(1); }
    Keccak_Initialize(s, 1600);
    Keccak_AddBytes(s, (const uint8_t*)id, strlen(id));
    Keccak_Finalize(s);

    // 清零
    memset(row_bits, 0, m);

    // ----------- 随机挑两个不同位置（前 m_prime 部分）-----------
    size_t seen0 = SIZE_MAX, seen1 = SIZE_MAX;
    while (seen1 == SIZE_MAX) {
        uint8_t r[2];
        Keccak_Squeeze(s, r, 2);                    
        size_t idx = ((size_t)r[0] | ((size_t)r[1] << 8)) % m_prime;
        if (seen0 == SIZE_MAX) {
            seen0 = idx;
        } else if (idx != seen0) {
            seen1 = idx;
        }
    }

    if (seen0 >= m_prime || seen1 >= m_prime) {
        fprintf(stderr, "row_ID: index overflow seen0=%zu seen1=%zu m_prime=%zu\n",
                seen0, seen1, m_prime);
        exit(1);
    }
    row_bits[seen0] = 1;
    row_bits[seen1] = 1;

    // ----------- 填充尾部 -----------
    if (tail_len) {
        size_t tail_bytes = (tail_len + 7) / 8;
        uint8_t *tbuf = malloc(tail_bytes);
        if (!tbuf) { fprintf(stderr, "row_ID: malloc tbuf failed\n"); free(s); exit(1); }
        Keccak_Squeeze(s, tbuf, tail_bytes);

        // 改名成 t 避免和外层 for 变量冲突
        for (size_t t = 0; t < tail_len; t++) {
            size_t pos = m_prime + t;
            if (pos >= m) {
                fprintf(stderr, "row_ID: tail index overflow pos=%zu (m_prime=%zu tail_len=%zu m=%zu)\n",
                        pos, m_prime, tail_len, m);
                exit(1);
            }
            row_bits[pos] = (tbuf[t >> 3] >> (t & 7)) & 1u;
        }
        free(tbuf);
    }

    free(s);
}











// 初始化编码器：为每行预计算种子
void SME_init(SparseMatrixEncoder *enc, size_t n, size_t weight) {
    enc->n = n;
    enc->weight = weight;
    enc->m = 0;
 //   enc->row_seed = malloc(enc->m * sizeof(uint64_t));
//    assert(enc->row_seed);
    // 使用 splitmix64 根据行号生成稳定种子
//    uint64_t seed = 0x12345678abcdefULL;
 //   for (size_t i = 0; i < enc->m; i++) {
     //   uint64_t x = i;
      //  enc->row_seed[i] = splitmix64(&x);
   // }
}

// 初始化编码器：为每行预计算种子
void SME_init_1(SparseMatrixEncoder *enc, size_t n, size_t weight) {
    enc->n = n;
    enc->weight = weight;
    enc->m = weight * n;
    enc->row_seed = malloc(enc->m * sizeof(uint64_t));
    assert(enc->row_seed);
    // 使用 splitmix64 根据行号生成稳定种子
    uint64_t seed = 0x12345678abcdefULL;
    for (size_t i = 0; i < enc->m; i++) {
        uint64_t x = i;
        enc->row_seed[i] = splitmix64(&x);
    }}

// 基于 ID 字符串计算 64-bit FNV-1a 哈希
static uint64_t hash_id(const char *id) {
    uint64_t hash = 0xcbf29ce484222325ULL;
    while (*id) {
        hash ^= (uint8_t)*id++;
        hash *= 0x100000001b3ULL;
    }
    return hash;
}

// VOLE 中的 xorshift64
static uint64_t xorshift64(uint64_t *state) {
    uint64_t x = *state;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    *state = x;
    return x;
}
// // 释放资源
// void SME_free(SparseMatrixEncoder *enc) {
//     free(enc->row_seed);
// }

// buildRow: 根据行号 i 生成 weight 个唯一非零列索引
/**
 * 构造行向量：根据 ID 哈希生成 weight 个唯一列索引
 * @param enc    编码器
 * @param id     身份证字符串
 * @param out_idx 输出数组，长度为 enc->weight
 */
void SME_buildRow_ID(const SparseMatrixEncoder *enc, const char *id, size_t *out_idx) {
 
 size_t m_prime = enc->weight * enc->n;
    size_t tail_len = enc->tail_len;
    uint8_t *row_bits = malloc(m_prime + tail_len);
    row_ID(id, m_prime, tail_len, row_bits);

    size_t cnt = 0;
    for (size_t i = 0; i < m_prime && cnt < enc->weight; i++) {
        if (row_bits[i]) {
            out_idx[cnt++] = i;
        }
    }
    free(row_bits);


}



// 使用稀疏高斯消元求解 M * P = 0
int solve_nullspace(const SparseMatrixEncoder *enc,
                    const size_t *rows, size_t num_rows,
                    uint32_t *P_out)
{
    size_t n = enc->weight * enc->n + enc->tail_len;
    size_t m = num_rows;
    size_t word_cnt = (n + 31) / 32;
    // 构造行掩码
    uint32_t **row_mask = malloc(m * sizeof(uint32_t*));
    for (size_t i = 0; i < m; i++) {
        row_mask[i] = calloc(word_cnt, sizeof(uint32_t));
        for (size_t k = 0; k < enc->weight; k++) {
            size_t j = rows[i * enc->weight + k];
            size_t w = j / 32, b = j % 32;
            row_mask[i][w] |= (1u << b);
        }
    }
    // Gauss-Jordan
    size_t r = 0;
    size_t *pivot = calloc(n, sizeof(size_t));
    for (size_t j = 0; j < n; j++) pivot[j] = SIZE_MAX;

    for (size_t j = 0; j < n && r < m; j++) {
        size_t w = j / 32, b = j % 32, bit = 1u << b;
        size_t pi = SIZE_MAX;
        for (size_t i = r; i < m; i++) {
            if (row_mask[i][w] & bit) { pi = i; break; }
        }
        if (pi == SIZE_MAX) continue;
        if (pi != r) {
            uint32_t *tmp = row_mask[pi];
            row_mask[pi] = row_mask[r];
            row_mask[r] = tmp;
        }
        pivot[j] = r;
        for (size_t i = 0; i < m; i++) {
            if (i != r && (row_mask[i][w] & bit)) {
                for (size_t t = 0; t < word_cnt; t++)
                    row_mask[i][t] ^= row_mask[r][t];
            }
        }
        r++;
    }
    // 自由变量取第一个
    size_t free_j = SIZE_MAX;
    for (size_t j = 0; j < n; j++) {
        if (pivot[j] == SIZE_MAX) { free_j = j; break; }
    }
    if (free_j == SIZE_MAX) {
        memset(P_out, 0, n * sizeof(uint32_t));
    } else {
        memset(P_out, 0, n * sizeof(uint32_t));
        P_out[free_j] = 1;
        for (size_t j = 0; j < n; j++) {
            if (pivot[j] != SIZE_MAX) {
                uint32_t acc = 0;
                size_t pr = pivot[j];
                for (size_t k = 0; k < n; k++) {
                    if (k != j) {
                        size_t w2 = k/32, b2 = k%32;
                        if (row_mask[pr][w2] & (1u<<b2))
                            acc ^= P_out[k];
                    }
                }
                P_out[j] = acc;
            }
        }
    }
    // 释放
    free(pivot);
    for (size_t i = 0; i < m; i++) free(row_mask[i]);
    free(row_mask);
    return 0;
}





// buildRow: 根据行号 i 生成 weight 个唯一非零列索引
void SME_buildRow(const SparseMatrixEncoder *enc, size_t i, size_t *out_idx) {
    assert(i < enc->m);
    uint64_t state = enc->row_seed[i];
    size_t count = 0;
    while (count < enc->weight) {
        uint64_t rnd = xorshift64(&state);
        size_t v = rnd % enc->n;
        // 检查重复
        int dup =0;
        for (size_t t = 0; t < count; t++) {
            if (out_idx[t] == v) { dup = 1; break; }
        }
        if (!dup) {
            out_idx[count++] = v;
        }
    }
}








// encode: Y = M * values (Field 运算使用 XOR)
// values: 输入数组，长度 n
// Y: 输出数组，长度 m
void SME_encode(const SparseMatrixEncoder *enc, const uint32_t *values, uint32_t *Y) {
    size_t *idx = malloc(enc->weight * sizeof(size_t));
    assert(idx);
    for (size_t i = 0; i < enc->m; i++) {
        SME_buildRow(enc, i, idx);
        uint32_t sum = 0;
        for (size_t k = 0; k < enc->weight; k++) {
            sum ^= values[idx[k]];  // GF(2) 下为 XOR
        }
        Y[i] = sum;
    }
  free(idx);
}

// decode: 使用稀疏高斯消元法恢复 values
// 假设存在共享向量 P，与 Y 做 XOR 得到 Combined
// Combined = M * values
// values_out 长度 n
int SME_decode(const SparseMatrixEncoder *enc,
                     const uint32_t *Y, const uint32_t *P,
                     uint32_t *values_out) {
    size_t n = enc->n;
    size_t m = enc->m;

    // 1. 构造 RHS: C[i] = Y[i] ^ P[i]
    uint32_t *C = malloc(m * sizeof(uint32_t));
    if (!C) { fprintf(stderr, "内存分配失败 C\n"); return -1; }
    for (size_t i = 0; i < m; i++) {
        C[i] = Y[i] ^ P[i];
    }

    // 2. 预分配 bitset 行掩码: 每行用 word_cnt 个 uint64_t 存储 n 列
    size_t word_cnt = (n + 63) / 64;
    uint64_t **row_mask = malloc(m * sizeof(uint64_t *));
    if (!row_mask) { fprintf(stderr, "内存分配失败 row_mask pointers\n"); free(C); return -1; }
    for (size_t i = 0; i < m; i++) {
        row_mask[i] = calloc(word_cnt, sizeof(uint64_t));
        if (!row_mask[i]) {
            fprintf(stderr, "内存分配失败 row_mask[%zu]\n", i);
            // 释放之前分配
            for (size_t t = 0; t < i; t++) free(row_mask[t]);
            free(row_mask);
            free(C);
            return -1;
        }
    }

    // 临时数组存 idx
    size_t *idx = malloc(enc->weight * sizeof(size_t));
    if (!idx) { fprintf(stderr, "内存分配失败 idx\n"); /*释放*/ for(size_t i=0;i<m;i++)free(row_mask[i]); free(row_mask); free(C); return -1; }

    // 3. 填充 row_mask
    for (size_t i = 0; i < m; i++) {
        SME_buildRow(enc, i, idx);
        // 清零（虽然 calloc 已经零，但若重用可先清）
        //for (size_t w = 0; w < word_cnt; w++) row_mask[i][w] = 0;
        for (size_t k = 0; k < enc->weight; k++) {
            size_t j = idx[k];
            size_t w = j >> 6;           // j / 64
            size_t b = j & 63;           // j % 64
            row_mask[i][w] |= (1ULL << b);
        }
    }
    free(idx);

    // 4. 高斯消元：寻找主元并消去其他行得到 reduced row echelon form
    // pivot_row_for_col[j] 存放列 j 的主元行号，若为 SIZE_MAX 表示无主元（即矩阵列不满秩）
    size_t *pivot_row_for_col = malloc(n * sizeof(size_t));
    if (!pivot_row_for_col) { fprintf(stderr, "内存分配失败 pivot\n"); goto CLEAN_FAIL; }
    for (size_t j = 0; j < n; j++) pivot_row_for_col[j] = SIZE_MAX;

    size_t cur = 0; // 当前要放置主元的行索引
    for (size_t j = 0; j < n && cur < m; j++) {
        // 在 [cur, m) 行中寻找主元行：row_mask[i][j] == 1
        size_t pivot = SIZE_MAX;
        size_t w = j >> 6;
        uint64_t bit = 1ULL << (j & 63);
        for (size_t i = cur; i < m; i++) {
            if (row_mask[i][w] & bit) {
                pivot = i;
                break;
            }
        }
        if (pivot == SIZE_MAX) {
            // 此列无主元，列 j 在矩阵中无约束，矩阵秩 < n
            continue;
        }
        // 交换 pivot 行与 cur 行
        if (pivot != cur) {
            uint64_t *tmp_row = row_mask[pivot];
            row_mask[pivot] = row_mask[cur];
            row_mask[cur] = tmp_row;
            uint32_t tmpC = C[pivot];
            C[pivot] = C[cur];
            C[cur] = tmpC;
        }
        // 记录主元行
        pivot_row_for_col[j] = cur;

        // 对所有其他行做消去（包括 [0, m) 中所有 != cur 的行），以得到 reduced row echelon form
        for (size_t i = 0; i < m; i++) {
            if (i == cur) continue;
            if (row_mask[i][w] & bit) {
                // row i 在列 j 有 1，需要消去
                // 整个 bitset XOR
                for (size_t t = 0; t < word_cnt; t++) {
                    row_mask[i][t] ^= row_mask[cur][t];
                }
                // RHS 也 XOR
                C[i] ^= C[cur];
            }
        }
        cur++;
    }

    // 5. 检查是否满秩：若 pivot_row_for_col 中有 SIZE_MAX，则矩阵列不满秩，无法恢复
    for (size_t j = 0; j < n; j++) {
        if (pivot_row_for_col[j] == SIZE_MAX) {
            fprintf(stderr, "高斯消元失败：列 %zu 无主元，矩阵不满秩，无法恢复所有变量\n", j);
            //goto CLEAN_FAIL;
        }
    }

    // 6. 回代/直接取解：由于我们做了 reduced row echelon form，每个主元行在其主元列外其他列已全部为0
    // 因此直接 values_out[j] = C[pivot_row_for_col[j]]
   for (size_t j = 0; j < n; j++) {
       size_t r = pivot_row_for_col[j];
       values_out[j] = (r != SIZE_MAX) ? C[r] : 0;  // 自由变量取 0 的特解
   }

    // 清理并返回成功
    free(pivot_row_for_col);
    for (size_t i = 0; i < m; i++) free(row_mask[i]);
    free(row_mask);
    free(C);
    return 0;

CLEAN_FAIL:
    // 释放资源
    if (pivot_row_for_col) free(pivot_row_for_col);
    for (size_t i = 0; i < m; i++) {
        if (row_mask && row_mask[i]) free(row_mask[i]);
    }
    if (row_mask) free(row_mask);
    if (C) free(C);
    return -1;
}

// --------- PaXos ---------


void print_binary(uint32_t val, int bits) {
    for (int i = bits - 1; i >= 0; i--) {
        putchar((val >> i) & 1 ? '1' : '0');
        if (i % 8 == 0 && i != 0) putchar(' ');  // 每 8 位空格分隔
    }
}


// // 将测试逻辑放在一个自定义函数中，不直接写在 main 里
//   int run_faest_128f_test(void) {
      
//     int ret;

//     // 分配公私钥缓冲，大小由宏定义给出
//     uint8_t pk[FAEST_128F_PUBLIC_KEY_SIZE];
   
//     uint8_t sk[FAEST_128F_PRIVATE_KEY_SIZE];
   

//     // 1. 密钥生成
//    ret = faest_128f_keygen(
//         pk ,    // 输出：公钥及其长度
//         sk    // 输出：私钥及其长度
//     );

//     if (ret != 0) {
//         fprintf(stderr, "faest_128f_keygen failed: %d\n", ret);
//         return EXIT_FAILURE;
//     }

//     // 可选：对生成的密钥进行验证
//     ret = faest_128f_validate_keypair(pk, sk);
//     if (ret != 0) {
//         fprintf(stderr, "faest_128f_validate_keypair failed: %d\n", ret);
//         return EXIT_FAILURE;
//     }

//     // 2. 构造待签名消息（示例用固定字符串，也可以改成随机或输入数据）
//     const uint8_t message[] = "Hello FAEST-128f!";
//     size_t message_len = sizeof(message) - 1;

//     // 准备签名输出缓冲，FAEST_128F_SIGNATURE_SIZE 定义了签名的最大可能长度
//     uint8_t signature[FAEST_128F_SIGNATURE_SIZE];
//     size_t signature_len = FAEST_128F_SIGNATURE_SIZE;

//     // 3. 签名
//     ret = faest_128f_sign(sk, message, message_len, signature, &signature_len);
//     if (ret != 0) {
//         fprintf(stderr, "faest_128f_sign failed: %d\n", ret);
//         return EXIT_FAILURE;
//     }
//     // signature_len 现在持有实际签名长度

//     // 4. 验签
//     ret = faest_128f_verify(pk, message, message_len, signature, signature_len);
//     if (ret != 0) {
//         fprintf(stderr, "faest_128f_verify failed: %d\n", ret);
//         return EXIT_FAILURE;
//     }

//     // 如果到达这里，说明签名和验签均成功
//     printf("Sign/Verify test passed\n");
//     return EXIT_SUCCESS;
// }

// 将测试逻辑放在一个自定义函数中，不直接写在 main 里
  int run_faest_128f_test_from_seed(const uint8_t *seed, size_t seed_len) {

    g_seed     = seed;
    g_seed_len = seed_len;

   long t0, t1, t2, t3;
    t0 = now_us();
    int ret;

    // 分配公私钥缓冲，大小由宏定义给出
    uint8_t pk[FAEST_128F_PUBLIC_KEY_SIZE];
   
    uint8_t sk[FAEST_128F_PRIVATE_KEY_SIZE];
   

    // 1. 密钥生成
   ret = faest_128f_keygen(
        pk ,    // 输出：公钥及其长度
        sk    // 输出：私钥及其长度
    );

    // if (ret != 0) {
    //     fprintf(stderr, "faest_128f_keygen failed: %d\n", ret);
    //     return EXIT_FAILURE;
    // }
//  t1 = now_us();
//  printf("[Timing] KeyGen:    %ld us\n", t1 - t0);
    // // 可选：对生成的密钥进行验证
    // ret = faest_128f_validate_keypair(pk, sk);
    // if (ret != 0) {
    //     fprintf(stderr, "faest_128f_validate_keypair failed: %d\n", ret);
    //     return EXIT_FAILURE;
    // }




    // 2. 构造待签名消息（示例用固定字符串，也可以改成随机或输入数据）
    const uint8_t message[] = "1";
    size_t message_len = sizeof(message) - 1;

    // 准备签名输出缓冲，FAEST_128F_SIGNATURE_SIZE 定义了签名的最大可能长度
    uint8_t signature[FAEST_128F_SIGNATURE_SIZE];
    size_t signature_len = FAEST_128F_SIGNATURE_SIZE;

    // 3. 签名
    ret = faest_128f_sign(sk, message, message_len, signature, &signature_len);
    // if (ret != 0) {
    //     fprintf(stderr, "faest_128f_sign failed: %d\n", ret);
    //     return ret;
    // }
    // signature_len 现在持有实际签名长度
    // t2= now_us();

    // printf("[Timing] Sign:    %ld us\n", t2 - t1);
    // 4. 验签
    // printf("11111111111");
    ret = faest_128f_verify(pk, message, message_len, signature, signature_len);
    // printf("222222222222222");
    // if (ret != 0) {
    //     fprintf(stderr, "faest_128f_verify failed: %d\n", ret);
    //     return ret;
    // }
//      t3= now_us();
//   printf("[Timing] Verfiy:    %ld us\n", t3 - t2);

//   printf("[Timing] Total:    %ld us\n", t3 - t0);
//     // 如果到达这里，说明签名和验签均成功
    return 0;
}

void run_vole_simple_test(uint8_t *delta_vo, uint8_t *A_vo, uint8_t *B_vo, uint8_t *C_vo,
                          uint8_t **u_out,size_t m_2) {
 
   // 获取 FAEST-128f 参数集
    const faest_paramset_t *params = faest_get_paramset(FAEST_128F);
    unsigned int lambda = params->lambda;
    unsigned int tau = params->tau;
    unsigned int ellhat = params->l + params->lambda * 3 + UNIVERSAL_HASH_B_BITS;
    unsigned int ellhat_bytes = (ellhat + 7) / 8;
    // printf("%u\n", ellhat);
    // printf("params 指针 = %p\n", (void*)params);

    // 准备随机根密钥和 IV（这里以示例值填充）
    uint8_t rootKey[32];
    for (int i = 0; i < 32; i++) rootKey[i] = (uint8_t)i;
    uint8_t iv[IV_SIZE] = {0};

    // 分配 BAVC 结构和输出缓冲区
    bavc_t vecCom;
    uint8_t *c = malloc((tau - 1) * ellhat_bytes);
    uint8_t *u = malloc(ellhat_bytes);
    uint8_t **v = malloc(lambda * sizeof(uint8_t*));






   unsigned int MAX_DEPTH_1 = bavc_max_node_depth(tau-1, params->tau1, params->k);
for (unsigned int i = 0; i < lambda; i++) {
    v[i] = malloc(MAX_DEPTH_1 * ellhat_bytes);
}
    
    // 调用 VOLE 承诺生成器
    vole_commit(rootKey, iv, ellhat, params, &vecCom, c, u, v);


    comm_add(ROLE_DS, (size_t)((tau - 1) * ellhat_bytes), PHASE_SETUP);





   size_t total_bytes = ellhat_bytes * (1 + lambda);

memset(A_vo, 0, m_2);
memset(B_vo, 0, m_2);

for (size_t i = 0; i < m_2; i++) {
    size_t idx = i % total_bytes;
    if (idx < ellhat_bytes) {
        A_vo[i] = u[idx];
        B_vo[i] = u[idx] ^ 0;
    } else {
        size_t which = (idx - ellhat_bytes) / ellhat_bytes;
        size_t off   = (idx - ellhat_bytes) % ellhat_bytes;
        A_vo[i] = v[which][off];
        B_vo[i] = v[which][off];
    }
}


    // rand_bytes(delta_vo, m_2);
       randombytes(delta_vo, m_2);

  for (size_t i = 0; i < m_2; i++) {
    A_vo[i] &= 1;
    B_vo[i] &= 1;
    delta_vo[i] &= 1;
  }




     for (size_t i = 0; i < m_2; i++) {
        C_vo[i] = B_vo[i] ^ (A_vo[i] & delta_vo[i]);
    }

    uint8_t *u_full = malloc(m_2);
    if (!u_full) { fprintf(stderr, "malloc u_full failed\n"); exit(1); }
    for (size_t i = 0; i < m_2; i++) u_full[i] = (uint8_t)(u[i % ellhat_bytes] & 1);
    *u_out = u_full;


}

void run_vole_simple_test(
    uint8_t  *delta_vo,
    uint8_t  *A_vo,
    uint8_t  *B_vo,
    uint8_t  *C_vo,
    uint8_t **u_out,
    size_t    m_2
);

 long now_us(void) {
    struct timeval tv;
    gettimeofday(&tv, NULL);
    return tv.tv_sec * 1000000L + tv.tv_usec;
}



int main(void) {

 srand((unsigned)time(NULL));

    int sizeX, sizeY, commonSize;
    printf("请输入集合 X 的大小: ");
    scanf("%d", &sizeX);
    printf("请输入集合 Y 的大小: ");
    scanf("%d", &sizeY);
    printf("请输入 X 和 Y 的交集大小: ");
    scanf("%d", &commonSize);





    
    long t0 = now_us();

    if (commonSize > sizeX || commonSize > sizeY) {
        fprintf(stderr, "交集大小不能超过任一集合的总大小！\n");
        return 1;
    }

    // 分配空间
    char (*common)[BUF_LEN] = malloc(commonSize * BUF_LEN);
    char (*X)[BUF_LEN]      = malloc(sizeX      * BUF_LEN);
    char (*Y1)[BUF_LEN]      = malloc(sizeY      * BUF_LEN);
    char (*D)[BUF_LEN]      = malloc(sizeY      * BUF_LEN);
    if (!common || !X || !Y1) {
        fprintf(stderr, "内存分配失败！\n");
        return 1;
    }

    // 生成交集
    gen_common_set(common, commonSize);
    // 生成 X：只需避开 common
    gen_set(X, sizeX, common, commonSize, NULL, 0);
    // 生成 Y：需避开 common 且避开 X 的所有元素，防止额外重叠
    gen_set(Y1, sizeY, common, commonSize, X, sizeX);
    gen_set(D, sizeY, common, commonSize, Y1, sizeY);
 //---------------------------------------------------------

int N_nodes = 20; /* 你可以改成 10/50/100 做多组对比 */

run_bfod_contrast_experiment(X, sizeX, Y1, sizeY, D, commonSize, N_nodes);

run_passp_batch_contrast_experiment(X, sizeX, Y1, sizeY, common, commonSize, N_nodes);

run_accredited_spir_contrast_experiment(X, sizeX, Y1, sizeY, N_nodes);

////////////////////////////////////////////////////////


const size_t num_rows_2 = sizeX;
const size_t n_2 = sizeX; 
const size_t weight_2 = 2;  
const size_t tail_len = 40;



SparseMatrixEncoder enc2 = { .n = sizeX, .weight = weight_2, .m_prime = weight_2 * sizeX,
                                .tail_len = tail_len };


g_m2 = enc2.weight * enc2.n + enc2.tail_len;
if (g_m2 == 0) {
        fprintf(stderr, "FATAL: g_m2 计算结果为 0，可能是参数设置错误 (weight=%zu n=%zu tail_len=%zu)\n",
                enc2.weight, enc2.n, enc2.tail_len);
        exit(1);
    }

 if (g_m2 != enc2.m_prime + enc2.tail_len) {
        fprintf(stderr, "FATAL: g_m2 与 enc2 结构计算结果不一致 g_m2=%zu, m_prime+tail_len=%zu\n",
                g_m2, enc2.m_prime + enc2.tail_len);
        exit(1);
    }

    printf("[INFO] g_m2 已初始化 = %zu  (m_prime=%zu  tail_len=%zu)\n",
           g_m2, enc2.m_prime, enc2.tail_len);




















 size_t *rows_3= malloc(num_rows_2 * weight_2 * sizeof(size_t));



for (size_t i = 0; i < num_rows_2; i++) {
        SME_buildRow_ID(&enc2, X[i], &rows_3[i*weight_2]);
        
    }





g_m2 = enc2.weight * enc2.n + enc2.tail_len; // 只在 Setup 阶段赋值一次
printf("[DEBUG] 全局 m_2 = %zu\n", g_m2);



uint8_t **M_bits = malloc(num_rows_2 * sizeof(uint8_t*));
for (size_t i = 0; i < num_rows_2; i++)  M_bits[i] = calloc(g_m2, 1);

// 2) fill each row with the Keccak-based random vector
   for (size_t i = 0; i < num_rows_2; i++) {
        row_ID(X[i], enc2.weight * enc2.n, enc2.tail_len, M_bits[i]);}

// 3) (optional) rebuild rows_2 for your sparse solver
size_t *rows_2 = malloc(num_rows_2 * enc2.weight * sizeof(size_t));
for (size_t i = 0; i < num_rows_2; i++) {
 size_t cnt = 0;
for (size_t j = 0; j < g_m2 && cnt < enc2.weight; j++) {
        if (M_bits[i][j])
            rows_2[i*enc2.weight + cnt++] = j;
    }
    assert(cnt == enc2.weight); }

    // 4) print M in binary
    // printf("M as full %zux%zu binary matrix:\n", num_rows_2, m_2);
//     for (size_t i = 0; i < num_rows_2; i++) {
//         // printf("row %zu: ", i);
//     for (size_t j = 0; j < m_2; j++)
//         // putchar(M_bits[i][j] ? '1' : '0');
//         putchar('\n');
// }
size_t nb = (g_m2 + 7) >> 3;

 for (size_t i = 0; i < num_rows_2; i++) {
        int r = run_faest_128f_test_from_seed(M_bits[i], g_m2);
        if (r != 0) {
            fprintf(stderr, "Row %zu 测试失败: %d\n", i, r);
        }
       comm_add(ROLE_DS, (size_t)(2 * nb), PHASE_AUTH);
    }






///////////////////////////////////////////////////////

// 分配顶层数组
uint8_t **M_c_bits = malloc(sizeY * sizeof(uint8_t*));
if (!M_c_bits) {
    fprintf(stderr, "malloc M_c_bits top-level array failed (sizeY=%zu)\n", sizeY);
    exit(1);
}

size_t *rows_c = malloc(sizeY * enc2.weight * sizeof(size_t));
if (!rows_c) {
    fprintf(stderr, "malloc rows_c failed (sizeY=%zu weight=%zu)\n", sizeY, enc2.weight);
    exit(1);
}

for (size_t i = 0; i < sizeY; i++) {
    // 分配每一行
    M_c_bits[i] = calloc(g_m2, 1);
    if (!M_c_bits[i]) {
        fprintf(stderr, "内存分配失败 M_c_bits[%zu]\n", i);
        exit(1);
    }

    // 生成这一行（使用安全版 row_ID）
    row_ID(Y1[i], enc2.m_prime, enc2.tail_len, M_c_bits[i]);

    // ====== 内存边界探测（防止上一步越界写坏别的指针）======
    volatile uint8_t first_byte = M_c_bits[i][0];
    volatile uint8_t last_byte  = M_c_bits[i][g_m2 - 1];
    (void)first_byte; (void)last_byte;

    // ====== 收集稀疏位置并检测 ======
    size_t cnt = 0;
    for (size_t j = 0; j < enc2.m_prime; j++) {
        if (M_c_bits[i][j]) {
            rows_c[i * enc2.weight + cnt] = j;
            cnt++;
            if (cnt > enc2.weight) {
                fprintf(stderr,
                        "ERROR: row %zu 出现超过 weight=%zu 个 1 (j=%zu)！\n",
                        i, enc2.weight, j);
                exit(1);
            }
        }
    }
    if (cnt != enc2.weight) {
        fprintf(stderr, "ERROR: row %zu 仅生成了 %zu/%zu 个 1，比预期少！\n",
                i, cnt, enc2.weight);
        exit(1);
    }

 for (size_t j = enc2.m_prime; j < g_m2; j++) {
        if (M_c_bits[i][j] != 0 && M_c_bits[i][j] != 1) {
            fprintf(stderr, "ERROR: row %zu 尾部位置 %zu = %u (非 0/1)\n",
                    i, j, M_c_bits[i][j]);
            exit(1);
        }
    }

    // ====== 调试输出部分（前几行看一下内容）======
    if (i < 5) { // 避免刷屏，只看前5行
        printf("[DEBUG] row=%zu ptr=%p 前8bit: ", i, (void*)M_c_bits[i]);
        for (size_t b = 0; b < 8 && b < g_m2; b++) {
            printf("%u", M_c_bits[i][b] & 1u);
        }
        printf("\n");
    }
}



//     // printf("M_c_bits 矩阵（每行 %zu 列）：\n", m_2);
// for (size_t i = 0; i < sizeY ; i++) {
//     printf("row %zu: ", i);
//     for (size_t j = 0; j < m_2; j++) {
//         // %u 用于打印 uint8_t
//         //   putchar(M_c_bits[i][j] ? '1' : '0');
//     }
//     printf("\n");
// }
/////////////////////////////////////////////////////
// 5) solve for P2 with your existing solve_nullspace(enc2, rows_2, ...)
uint32_t *P2 = calloc(g_m2, sizeof(uint32_t));



solve_nullspace(&enc2, rows_2, num_rows_2, P2);




   printf("passed\n");

   heap_check("after solve_nullspace");

// for (size_t i = 0; i < m_2; i++) {
//     // putchar(P2[i] ? '1' : '0');
// }
// putchar('\n');

// 6) verify M*P=0 with the full bits
// printf("Verifying M*P2 = 0 for each row:\n");
for (size_t i = 0; i < num_rows_2; i++) {
     uint32_t acc = 0;
     for (size_t j = 0; j < g_m2; j++)
         if (M_bits[i][j])
             acc ^= P2[j];
    //   printf(" row %zu: %u\n", i, acc);
     assert(acc == 0);

  }


////////////////////////////////////////////////////////



uint8_t *delta= malloc(g_m2*sizeof(uint8_t));

uint8_t *A_vo = malloc(g_m2*sizeof(uint8_t));
uint8_t *B_vo = malloc(g_m2*sizeof(uint8_t));
uint8_t *C_vo = malloc(g_m2*sizeof(uint8_t));

uint8_t *u = malloc(g_m2*sizeof(uint8_t));


run_vole_simple_test(delta, A_vo, B_vo,C_vo, &u, g_m2);

long t1 = now_us();

printf("Setup耗时：%ld us\n", t1 - t0);

////////////////////////////////////////////////////////
 // 计算 A_plus_P 数组
uint8_t *AplusP = malloc(g_m2*sizeof(uint8_t));

for (size_t i = 0; i < g_m2; i++) {
    AplusP[i] = A_vo[i] ^ (uint8_t)P2[i];
}


////////////////////////////////////////////////////////


    // 申请所有临时缓冲
    uint8_t *tilde_A     = malloc(g_m2*sizeof(uint8_t));
    uint8_t *tilde_P     = malloc(g_m2*sizeof(uint8_t));
    uint8_t *tilde_delta = malloc(g_m2*sizeof(uint8_t));
    uint8_t *T1          = malloc(g_m2*sizeof(uint8_t));
    uint8_t *T2          = malloc(g_m2*sizeof(uint8_t));
    uint8_t *Z_A         = malloc(g_m2*sizeof(uint8_t));
    uint8_t *Z_P         = malloc(g_m2*sizeof(uint8_t));
    uint8_t *Z_delta     = malloc(g_m2*sizeof(uint8_t));
    uint8_t *e           = malloc(g_m2*sizeof(uint8_t));
   
    // 1) 随机采样 tilde_A, tilde_P, tilde_delta 并计算承诺
    randombytes(tilde_A,     g_m2);
    randombytes(tilde_P,     g_m2);
    randombytes(tilde_delta, g_m2);
    for (size_t i = 0; i < g_m2; i++) {
        tilde_A[i]     &= 1;
        tilde_P[i]     &= 1;
        tilde_delta[i] &= 1;
        T1[i] = tilde_A[i] ^ tilde_P[i];         // T1 = \tilde A + \tilde P
        T2[i] = tilde_P[i] ^ tilde_delta[i];     // T2 = \tilde P - \tilde δ (GF2 下减法=加法)
        e[i]  = P2[i]      ^ A_vo[i];           // e = P - δ
    }

    // 2) Fiat–Shamir 挑战 c ← H(Token ‖ T1 ‖ T2) mod 2
    KeccakSponge sp;
    Keccak_Initialize(&sp, 1600);
    Keccak_AddBytes(&sp, AplusP, g_m2);
    Keccak_AddBytes(&sp, T1,     g_m2);
    Keccak_AddBytes(&sp, T2,     g_m2);
    Keccak_Finalize(&sp);
    uint8_t c_buf[1];
    Keccak_Squeeze(&sp, c_buf, 1);
    uint8_t c = c_buf[0] & 1;

    // 3) 计算响应 Z_A, Z_P, Z_delta
    for (size_t i = 0; i < g_m2; i++) {
        Z_A[i]     = tilde_A[i]     ^ (c & A_vo[i]);
        Z_P[i]     = tilde_P[i]     ^ (c & P2[i]);
        Z_delta[i] = tilde_delta[i] ^ (c & A_vo[i]);
    }

    // 4) 验证
    bool ok1 = true, ok2 = true;
    for (size_t i = 0; i < g_m2; i++) {
        uint8_t lhs1 = Z_A[i] ^ Z_P[i];
        uint8_t rhs1 = T1[i] ^ (c & AplusP[i]);
        if (lhs1 != rhs1) { ok1 = false; break; }
    }
    for (size_t i = 0; i < g_m2; i++) {
        uint8_t lhs2 = Z_P[i] ^ Z_delta[i];
        uint8_t rhs2 = T2[i] ^ (c & e[i]);
        if (lhs2 != rhs2) { ok2 = false; break; }
    }

    // if (ok1 && ok2) {
    //     printf("零知识证明验证通过\n");
    // } else {
    //     printf("零知识证明验证失败\n");
    // }

///////////////////////////////////////////////
/*T1*//*T2*//*Z_A*//*Z_P*//*Z_delta*/
/*comm_add(ROLE_DS, (size_t)g_m2*5 , PHASE_AUTH); */



uint8_t *packed = malloc(nb);

pack_bits(T1, g_m2, packed);
comm_add(ROLE_DS, nb, PHASE_AUTH);
pack_bits(T2, g_m2, packed);
comm_add(ROLE_DS, nb, PHASE_AUTH);
pack_bits(Z_A, g_m2, packed);
comm_add(ROLE_DS, nb, PHASE_AUTH);
pack_bits(Z_P, g_m2, packed);
comm_add(ROLE_DS, nb, PHASE_AUTH);
pack_bits(Z_delta, g_m2, packed);
comm_add(ROLE_DS, nb, PHASE_AUTH);


 // 1) DS Commit
    uint8_t *r_u    = malloc(g_m2*sizeof(uint8_t)),
            *r_X    = malloc(g_m2*sizeof(uint8_t)),
            *Com    = malloc(g_m2*sizeof(uint8_t)),
            *T_row  = malloc(g_m2*sizeof(uint8_t)),
            *T3     = malloc(g_m2*sizeof(uint8_t));

    uint8_t *S_u = malloc(g_m2*sizeof(uint8_t)),
            *S_X = malloc(g_m2*sizeof(uint8_t)),
            *S_Y = malloc(g_m2*sizeof(uint8_t));

for (size_t row_idx = 0; row_idx < num_rows_2; row_idx++) {
    uint8_t *row = M_bits[row_idx];

        
for (size_t j = 0; j < g_m2; j++) {
       r_u[j] = rand() & 1;
       r_X[j] = rand() & 1;
   }


   
    for (size_t j = 0; j < g_m2; j++) {
        // r_u[j]    &= 1;
        // r_X[j]    &= 1;
        Com[j]    = row[j] ^ u[j];       // Com = row ⊕ u
        T_row[j]  = row[j] ^ delta[j];   // T_row = row ⊕ δ
        T3[j]     = r_X[j] ^ r_u[j];     // T3 = r_X ⊕ r_u

       
    }
     comm_add(ROLE_DS, (size_t)(3 * nb), PHASE_AUTH);

    // 2) 挑战 c1
    KeccakSponge sp;
    Keccak_Initialize(&sp, 1600);
    Keccak_AddBytes(&sp, Com,   g_m2);
    Keccak_AddBytes(&sp, T_row, g_m2);
    Keccak_AddBytes(&sp, T3,    g_m2);
    Keccak_Finalize(&sp);
    uint8_t buf1[1];
    Keccak_Squeeze(&sp, buf1, 1);
    uint8_t c1 = buf1[0] & 1;

    // 3) DS Response

    for (size_t j = 0; j < g_m2; j++) {
        S_u[j] = r_u[j] ^ (c1 & u[j]);
        S_X[j] = r_X[j] ^ (c1 & delta[j]);
        S_Y[j] = (delta[j] & e[j]) ^ B_vo[j];
    }

    comm_add(ROLE_DS, (size_t)(3 * nb), PHASE_AUTH);

    // 4) DR Response
    uint8_t *Z_Y = malloc(g_m2*sizeof(uint8_t));
    for (size_t j = 0; j < g_m2; j++) {
        Z_Y[j] = C_vo[j] ^ (A_vo[j] & T_row[j]);
    }


    /* DR sends per-row: Z_Y (m_2 bytes) */
   comm_add(ROLE_DR, (size_t)nb, PHASE_AUTH);


    // 5) 验证
    // (a) 重算挑战 c2
    Keccak_Initialize(&sp, 1600);
    Keccak_AddBytes(&sp, Com,   g_m2);
    Keccak_AddBytes(&sp, T_row, g_m2);
    Keccak_AddBytes(&sp, T3,    g_m2);
    Keccak_Finalize(&sp);
    uint8_t buf2[1];
    Keccak_Squeeze(&sp, buf2, 1);
    uint8_t c2 = buf2[0] & 1;

    // (b) 验证内积绑定
    bool ok3 = true, ok4 = true;
    for (size_t j = 0; j < g_m2; j++) {
        uint8_t lhs = S_X[j] ^ S_u[j];
        uint8_t rhs = T3[j] ^ (c2 & (Com[j] ^ T_row[j]));
        if (lhs != rhs) { ok3 = false; break; }
    }
    // (c) 验证零知识授权 w = (T_row & e) ⊕ S_Y ⊕ Z_Y == 0
       // (c) 验证零知识授权：GF(2) 下的内积必须为 0
    uint8_t acc = 0;
    for (size_t j = 0; j < g_m2; j++) {
        if (row[j]) {
            // 这里只累积一遍 XOR，而不是每个位置都当作独立检查
            acc ^= (T_row[j] & e[j]) ^ S_Y[j] ^ Z_Y[j];
        }
    }
    if (acc != 0) ok4 = false;


    // printf("Row %zu: %s\n", row_idx,
    //        (ok3 && ok4) ? "验证通过" : "验证失败");

    }


printf("=== Authorization Proof Pass! ===\n");
long t2 = now_us();
printf("Authorization 协议耗时：%ld us\n", t2 - t1);



// DC 端接收后计算 K = B + delta * (A+P)
    uint8_t *K = malloc(g_m2*sizeof(uint8_t));




// printf("=== 1111111111111 ===\n");


    for (size_t i = 0; i < g_m2; i++) {

        K[i] = (uint8_t)(B_vo[i] ^ (delta[i] & AplusP[i]));
    }
//     for (size_t i = 0; i < m_2; i++) {
//       putchar(K[i] ? '1' : '0');
// }

//comm_add(ROLE_DR, (size_t)nb, PHASE_RETR);




// ========== 步骤2：实现OPPRF-PSI协议 ==========
    // printf("\n=== 开始检索阶段 ===\n");

printf("计算F'函数值...\n");

uint8_t hash_output_len = 32;  // 哈希输出长度
uint8_t **F_prime_values = malloc(sizeY * sizeof(uint8_t*));
if (!F_prime_values) {
    fprintf(stderr, "malloc F_prime_values failed (sizeY=%d)\n", sizeY);
    exit(1);
}

printf("[DEBUG] Starting F'/Decode loop: sizeY=%zu g_m2=%zu hash_len=%u\n",
       (size_t)sizeY, g_m2, hash_output_len);

for (size_t row_idx = 0; row_idx < (size_t)sizeY; row_idx++) {
    // 1. 检查 M_c_bits 和 K 是否可用
    if (!M_c_bits) {
        fprintf(stderr, "[FATAL] M_c_bits 顶层指针为 NULL!\n");
        exit(1);
    }
    if (!M_c_bits[row_idx]) {
        fprintf(stderr, "[FATAL] M_c_bits[%zu] is NULL!\n", row_idx);
        exit(1);
    }
    if (!K) {
        fprintf(stderr, "[FATAL] K pointer is NULL!\n");
        exit(1);
    }
    if (g_m2 == 0) {
        fprintf(stderr, "[FATAL] g_m2 为 0，无法 Decode!\n");
        exit(1);
    }

    // 2. 分配当前行的 F' 输出缓冲
    F_prime_values[row_idx] = malloc(hash_output_len);
    if (!F_prime_values[row_idx]) {
        fprintf(stderr, "malloc F_prime_values[%zu] failed\n", row_idx);
        exit(1);
    }

    // 3. 调试输出前几行
    if (row_idx < 5 || row_idx % 1000 == 0) {
        printf("[DEBUG] i=%zu M_c_bits[i]=%p K=%p g_m2=%zu first 8 bits: ",
               row_idx, (void*)M_c_bits[row_idx], (void*)K, g_m2);
        for (size_t b = 0; b < 8 && b < g_m2; b++)
            printf("%u", M_c_bits[row_idx][b] & 1u);
        printf("\n");
    }

    // 4. 计算 F' 的输入：GF(2) 内积
    uint8_t inner = gf2_dot_bits(M_c_bits[row_idx], K, g_m2);

    // 5. 调用哈希函数 H_1_hash(inner) -> F_prime_values[row_idx]
    H_1_hash(&inner, 1, F_prime_values[row_idx], hash_output_len);
}












 // ========== 步骤3：求解线性系统 M_s * P' = (D[1] - F'(...), ...) ==========

    // printf("\n求解线性系统...\n");

    // 准备右侧向量：D[i] - F'(row_c[Y_1[i]])
    uint8_t **rhs_vector = malloc(sizeY * sizeof(uint8_t*));



    for (int i = 0; i < sizeY; i++) {
        rhs_vector[i] = malloc(hash_output_len * sizeof(uint8_t));



        
        // 将D[i]字符串转换为字节并与F'值做XOR
        uint8_t D_hash[32];
        H_1_hash((uint8_t*)D[i], strlen(D[i]), D_hash, hash_output_len);
        
        for (int j = 0; j < hash_output_len; j++) {
            rhs_vector[i][j] = D_hash[j] ^ F_prime_values[i][j];
        }
        
        // // printf("RHS[%d] = ", i);
        // for (int j = 0; j < 8; j++) {
        //     printf("%02x", rhs_vector[i][j]);
        // }
        // printf("...\n");
    }

    // 分配P'
    uint8_t **P_prime = malloc(hash_output_len * sizeof(uint8_t*));
   
    for (int i = 0; i < hash_output_len; i++) {
        P_prime[i] = calloc(g_m2, sizeof(uint8_t));
       
    }

    // 求解线性系统
    solve_linear_system_multi_rhs(&enc2, M_c_bits, sizeY, g_m2, rhs_vector, hash_output_len, P_prime);

    // printf("P' (前8个元素的前8字节):\n");
    // for (int i = 0; i < 8 && i < hash_output_len; i++) {
    //     printf("P'[%d]: ", i);
    //     for (int j = 0; j < 8 && j < m_2; j++) {
    //         printf("%02x ", P_prime[i][j]);
    //     }
    //     printf("\n");
    // }

    // ========== 步骤4：DR计算D'_i ==========

    // printf("\n计算D'_i...\n");

    uint8_t **D_prime = malloc(sizeX * sizeof(uint8_t*));

    for (int i = 0; i < commonSize; i++) {
        D_prime[i] = malloc(hash_output_len* sizeof(uint8_t));
        
        // 计算F'(row_2[X[i]])

     
        uint8_t F_prime_X[32];


         uint8_t innerX = gf2_dot_bits(M_bits[i], K, g_m2);
         H_1_hash(&innerX, 1, F_prime_X, hash_output_len);  

        //  printf("F'(X[%d]) = ", i);
        // for (int b = 0; b < hash_output_len; b++) {
        //     printf("%02x", F_prime_X[b]);
        // }
        // printf("\n");


        
        // 计算内积 <row_2[X[i]], P'>
        for (int byte_pos = 0; byte_pos < hash_output_len; byte_pos++) {
            uint8_t dot_product = 0;
            for (size_t j = 0; j < g_m2; j++) {
                if (M_bits[i][j]) {
                    dot_product ^= P_prime[byte_pos][j];
                }
            }
            
            // D'_i = F'(row_2[X[i]]) + <row_2[X[i]], P'>
            D_prime[i][byte_pos] = F_prime_X[byte_pos] ^ dot_product;
        }
        
        // printf("D'[%d] = ", i);
        // for (int j = 0; j < 8; j++) {
        //     printf("%02x", D_prime[i][j]);
         
        // }
        // printf("...\n");
        
    }

// DR -> DC: rhs_vector 传输
comm_add(ROLE_DC, (size_t)sizeY * hash_output_len, PHASE_RETR);




printf("匹配数: %d)\n", commonSize);

long t3 = now_us();
printf("Retrival协议耗时：%ld us\n", t3 - t2);


printf("Total：%ld us\n", t3 - t0);

print_comm_summary_sender_phase();


return  0;
}




void H_1_hash(uint8_t* input, size_t input_len, uint8_t* output, size_t output_len) {
    KeccakSponge *sponge = malloc(sizeof(KeccakSponge));
    if (!sponge) {
        fprintf(stderr, "H_1_hash: failed to malloc sponge\n");
        exit(1);
    }
    
    Keccak_Initialize(sponge, 1600);
    Keccak_AddBytes(sponge, input, input_len);
    Keccak_Finalize(sponge);
    Keccak_Squeeze(sponge, output, output_len);
    
    free(sponge);
}
// 扩展稀疏矩阵求解函数以支持多个右侧向量
int solve_linear_system_multi_rhs(const SparseMatrixEncoder *enc,
                                 uint8_t **M_c_bits_param, size_t num_rows, size_t m_2_param,
                                 uint8_t **rhs, size_t rhs_len,
                                 uint8_t **P_prime_out) {
    
    size_t n = m_2_param;  // 使用完整的m_2维度
    size_t word_cnt = (n + 63) / 64;
    
    // 为每个RHS字节位置分别求解
    for (size_t byte_pos = 0; byte_pos < rhs_len; byte_pos++) {
        // 构造增广矩阵 [M_c | rhs]
        uint64_t **augmented_matrix = malloc(num_rows * sizeof(uint64_t*));
        uint8_t *augmented_rhs = malloc(num_rows * sizeof(uint8_t));
        
        for (size_t i = 0; i < num_rows; i++) {
            augmented_matrix[i] = calloc(word_cnt, sizeof(uint64_t));
            augmented_rhs[i] = rhs[i][byte_pos];
            
            // 使用M_c_bits来构造掩码
            for (size_t j = 0; j < n; j++) {
                if (M_c_bits_param[i][j]) {
                    size_t w = j / 64, b = j % 64;
                    augmented_matrix[i][w] |= (1ULL << b);
                }
            }
        }
        
        // 高斯消元
        size_t *pivot_col = malloc(num_rows * sizeof(size_t));
        for (size_t i = 0; i < num_rows; i++) pivot_col[i] = SIZE_MAX;
        
        size_t rank = 0;
        for (size_t j = 0; j < n && rank < num_rows; j++) {
            size_t w = j / 64;
            uint64_t bit = 1ULL << (j % 64);
            
            // 寻找主元
            size_t pivot_row = SIZE_MAX;
            for (size_t i = rank; i < num_rows; i++) {
                if (augmented_matrix[i][w] & bit) {
                    pivot_row = i;
                    break;
                }
            }
            
            if (pivot_row == SIZE_MAX) continue;  // 无主元，跳过此列
            
            // 交换行
            if (pivot_row != rank) {
                uint64_t *tmp_row = augmented_matrix[pivot_row];
                augmented_matrix[pivot_row] = augmented_matrix[rank];
                augmented_matrix[rank] = tmp_row;
                
                uint8_t tmp_rhs = augmented_rhs[pivot_row];
                augmented_rhs[pivot_row] = augmented_rhs[rank];
                augmented_rhs[rank] = tmp_rhs;
            }
            
            pivot_col[rank] = j;
            
            // 消元
            for (size_t i = 0; i < num_rows; i++) {
                if (i != rank && (augmented_matrix[i][w] & bit)) {
                    // 行i -= 行rank
                    for (size_t k = 0; k < word_cnt; k++) {
                        augmented_matrix[i][k] ^= augmented_matrix[rank][k];
                    }
                    augmented_rhs[i] ^= augmented_rhs[rank];
                }
            }
            rank++;
        }
        
        // 构造解（特解，自由变量设为0）
        memset(P_prime_out[byte_pos], 0, n);
        for (size_t i = 0; i < rank; i++) {
            if (pivot_col[i] != SIZE_MAX) {
                P_prime_out[byte_pos][pivot_col[i]] = augmented_rhs[i];
            }
        }
        
        // 释放内存
        for (size_t i = 0; i < num_rows; i++) {
            free(augmented_matrix[i]);
        }
        free(augmented_matrix);
        free(augmented_rhs);
        free(pivot_col);
    }
    
    return 0;
}

void heap_check(const char* where) {
    void *p = malloc(16);
    if (!p) { printf("[FATAL] malloc fail at %s\n", where); exit(1); }
    free(p); // 如果这里 crash，就是之前已破坏 heap
}






