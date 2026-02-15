/* sha.c
 * Yongge Wang 
 *
 * Code was written: November 12, 2016-November 26, 2016
 *
 * sha.c implements SHA-1 (SHA-160), SHA256, and SHA512 for RLCE
 *
 * This code is for prototype purpose only and is not optimized
 *
 * Copyright (C) 2016 Yongge Wang
 * 
 * Yongge Wang
 * Department of Software and Information Systems
 * UNC Charlotte
 * Charlotte, NC 28223
 * yonwang@uncc.edu
 *
 */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>

#define ROTL(a,b) (((a) << (b)) | ((a) >> (32-(b))))
#define ROTR(a,b) (((a) >> (b)) | ((a) << (32-(b))))
#define CH(x,y,z) (((x) & (y)) ^ (~(x) & (z)))
#define MAJ(x,y,z) (((x) & (y)) ^ ((x) & (z)) ^ ((y) & (z)))
#define Sigma0(x) (ROTR(x,2) ^ ROTR(x,13) ^ ROTR(x,22))
#define Sigma1(x) (ROTR(x,6) ^ ROTR(x,11) ^ ROTR(x,25))
#define sigma0(x) (ROTR(x,7) ^ ROTR(x,18) ^ ((x) >> 3))
#define sigma1(x) (ROTR(x,17) ^ ROTR(x,19) ^ ((x) >> 10))

#define ROTL512(a,b) (((a) << (b)) | ((a) >> (64-(b))))
#define ROTR512(a,b) (((a) >> (b)) | ((a) << (64-(b))))
#define sigma5120(x) (ROTR512(x,1) ^ ROTR512(x,8) ^ ((x) >> 7))
#define sigma5121(x) (ROTR512(x,19) ^ ROTR512(x,61) ^ ((x) >> 6))
#define Sigma5120(x) (ROTR512(x,28) ^ ROTR512(x,34) ^ ROTR512(x,39))
#define Sigma5121(x) (ROTR512(x,14) ^ ROTR512(x,18) ^ ROTR512(x,41))

/* SHA-1 round macros */
#define SHA1_R0(A,B,C,D,E,W,K) { E += ROTL(A,5) + ((B & C) ^ ((~B) & D)) + W + K; B = ROTL(B, 30); }
#define SHA1_R1(A,B,C,D,E,W,K) { E += ROTL(A,5) + (B^C^D) + W + K; B = ROTL(B, 30); }
#define SHA1_R2(A,B,C,D,E,W,K) { E += ROTL(A,5) + ((B & C) ^ (B & D) ^ (C & D)) + W + K; B = ROTL(B, 30); }

/* SHA-256 round macro */
#define SHA256_ROUND(A,B,C,D,E,F,G,H,W,K) { \
    H += Sigma1(E) + CH(E,F,G) + K + W; \
    D += H; \
    H += Sigma0(A) + MAJ(A,B,C); \
}

/* SHA-512 round macro */
#define SHA512_ROUND(A,B,C,D,E,F,G,H,W,K) { \
    H += Sigma5121(E) + CH(E,F,G) + K + W; \
    D += H; \
    H += Sigma5120(A) + MAJ(A,B,C); \
}

void sha1_process(unsigned int[], unsigned char[]);
void sha256_process(unsigned int[], unsigned char[]);
void sha512_process(unsigned long [], unsigned char []);
int testSHA(int shatype, int numT);

int main (int argc, char *argv[]) {
  int numofT=100;
  testSHA(1,numofT);
  testSHA(2,numofT);
  testSHA(3,numofT);
  exit(0);
}


void sha_msg_pad(unsigned char message[], int size, unsigned int bitlen,
		 unsigned char paddedmsg[]) {
  int i;
  for (i=0; i<size; i++) {
    paddedmsg[i]=message[i];
  }
  paddedmsg[size]= 0x80;
  for (i=size+1; i<64; i++) {
    paddedmsg[i]=0x00;
  }
  paddedmsg[63] = bitlen;
  paddedmsg[62] = bitlen >> 8;
  paddedmsg[61] = bitlen >> 16;
  paddedmsg[60] = bitlen >> 24;
  return;
}

void sha_msg_pad0(unsigned int bitlen, unsigned char paddedmsg[]) {
  int i;
  for (i=0; i<64; i++) {
    paddedmsg[i]=0x00;
  }
  paddedmsg[63] = bitlen;
  paddedmsg[62] = bitlen >> 8;
  paddedmsg[61] = bitlen >> 16;
  paddedmsg[60] = bitlen >> 24;
  return;
}

void sha1_md(unsigned char message[], int size, unsigned int hash[5]) {
  unsigned int bitlen = 8*size;
  hash[0] = 0x67452301;
  hash[1] = 0xEFCDAB89;
  hash[2] = 0x98BADCFE;
  hash[3] = 0x10325476;
  hash[4] = 0xC3D2E1F0;
  int i;

  unsigned char msgTBH[64]; /* 64 BYTE msg to be hashed */
  unsigned char paddedMessage[64]; /* last msg block to be hashed*/

  int Q= size/64;
  int R= size%64;
  unsigned char msg[R];
  memcpy(msg, &message[64*Q], R * sizeof(unsigned char));
  
  for (i=0; i<Q; i++) {
    memcpy(msgTBH, &message[64*i], 64 * sizeof(unsigned char));
    sha1_process(hash, msgTBH);
  }
  if (R>55) {
    memcpy(msgTBH, msg, R * sizeof(unsigned char));
    msgTBH[R]=0x80;
    for (i=R+1; i<64; i++) {
      msgTBH[i]=0x00;
    } 
    sha1_process(hash, msgTBH);
    sha_msg_pad0(bitlen,paddedMessage);
  } else {
    sha_msg_pad(msg, R, bitlen, paddedMessage);
  }
  sha1_process(hash, paddedMessage);
  return;
}

void sha1_process(unsigned int hash[], unsigned char msg[]) {
  unsigned int W[80];
  register unsigned int A, B, C, D, E;
  int i;
  
  for(i = 0; i < 16; i++) {
    W[i] = (((unsigned) msg[i * 4]) << 24) +
      (((unsigned) msg[i * 4 + 1]) << 16) +
      (((unsigned) msg[i * 4 + 2]) << 8) +
      (((unsigned) msg[i * 4 + 3]));
  }
  for(i = 16; i < 80; i++) {
    W[i] = W[i-3] ^ W[i-8] ^ W[i-14] ^ W[i-16];
    W[i] = ROTL(W[i],1);
  }

  A = hash[0];
  B = hash[1];
  C = hash[2];
  D = hash[3];
  E = hash[4];

  /* Rounds 0-19: unrolled */
  SHA1_R0(A,B,C,D,E,W[0],0x5A827999);
  SHA1_R0(E,A,B,C,D,W[1],0x5A827999);
  SHA1_R0(D,E,A,B,C,W[2],0x5A827999);
  SHA1_R0(C,D,E,A,B,W[3],0x5A827999);
  SHA1_R0(B,C,D,E,A,W[4],0x5A827999);
  SHA1_R0(A,B,C,D,E,W[5],0x5A827999);
  SHA1_R0(E,A,B,C,D,W[6],0x5A827999);
  SHA1_R0(D,E,A,B,C,W[7],0x5A827999);
  SHA1_R0(C,D,E,A,B,W[8],0x5A827999);
  SHA1_R0(B,C,D,E,A,W[9],0x5A827999);
  SHA1_R0(A,B,C,D,E,W[10],0x5A827999);
  SHA1_R0(E,A,B,C,D,W[11],0x5A827999);
  SHA1_R0(D,E,A,B,C,W[12],0x5A827999);
  SHA1_R0(C,D,E,A,B,W[13],0x5A827999);
  SHA1_R0(B,C,D,E,A,W[14],0x5A827999);
  SHA1_R0(A,B,C,D,E,W[15],0x5A827999);
  SHA1_R0(E,A,B,C,D,W[16],0x5A827999);
  SHA1_R0(D,E,A,B,C,W[17],0x5A827999);
  SHA1_R0(C,D,E,A,B,W[18],0x5A827999);
  SHA1_R0(B,C,D,E,A,W[19],0x5A827999);

  /* Rounds 20-39: unrolled */
  SHA1_R1(A,B,C,D,E,W[20],0x6ED9EBA1);
  SHA1_R1(E,A,B,C,D,W[21],0x6ED9EBA1);
  SHA1_R1(D,E,A,B,C,W[22],0x6ED9EBA1);
  SHA1_R1(C,D,E,A,B,W[23],0x6ED9EBA1);
  SHA1_R1(B,C,D,E,A,W[24],0x6ED9EBA1);
  SHA1_R1(A,B,C,D,E,W[25],0x6ED9EBA1);
  SHA1_R1(E,A,B,C,D,W[26],0x6ED9EBA1);
  SHA1_R1(D,E,A,B,C,W[27],0x6ED9EBA1);
  SHA1_R1(C,D,E,A,B,W[28],0x6ED9EBA1);
  SHA1_R1(B,C,D,E,A,W[29],0x6ED9EBA1);
  SHA1_R1(A,B,C,D,E,W[30],0x6ED9EBA1);
  SHA1_R1(E,A,B,C,D,W[31],0x6ED9EBA1);
  SHA1_R1(D,E,A,B,C,W[32],0x6ED9EBA1);
  SHA1_R1(C,D,E,A,B,W[33],0x6ED9EBA1);
  SHA1_R1(B,C,D,E,A,W[34],0x6ED9EBA1);
  SHA1_R1(A,B,C,D,E,W[35],0x6ED9EBA1);
  SHA1_R1(E,A,B,C,D,W[36],0x6ED9EBA1);
  SHA1_R1(D,E,A,B,C,W[37],0x6ED9EBA1);
  SHA1_R1(C,D,E,A,B,W[38],0x6ED9EBA1);
  SHA1_R1(B,C,D,E,A,W[39],0x6ED9EBA1);

  /* Rounds 40-59: unrolled */
  SHA1_R2(A,B,C,D,E,W[40],0x8F1BBCDC);
  SHA1_R2(E,A,B,C,D,W[41],0x8F1BBCDC);
  SHA1_R2(D,E,A,B,C,W[42],0x8F1BBCDC);
  SHA1_R2(C,D,E,A,B,W[43],0x8F1BBCDC);
  SHA1_R2(B,C,D,E,A,W[44],0x8F1BBCDC);
  SHA1_R2(A,B,C,D,E,W[45],0x8F1BBCDC);
  SHA1_R2(E,A,B,C,D,W[46],0x8F1BBCDC);
  SHA1_R2(D,E,A,B,C,W[47],0x8F1BBCDC);
  SHA1_R2(C,D,E,A,B,W[48],0x8F1BBCDC);
  SHA1_R2(B,C,D,E,A,W[49],0x8F1BBCDC);
  SHA1_R2(A,B,C,D,E,W[50],0x8F1BBCDC);
  SHA1_R2(E,A,B,C,D,W[51],0x8F1BBCDC);
  SHA1_R2(D,E,A,B,C,W[52],0x8F1BBCDC);
  SHA1_R2(C,D,E,A,B,W[53],0x8F1BBCDC);
  SHA1_R2(B,C,D,E,A,W[54],0x8F1BBCDC);
  SHA1_R2(A,B,C,D,E,W[55],0x8F1BBCDC);
  SHA1_R2(E,A,B,C,D,W[56],0x8F1BBCDC);
  SHA1_R2(D,E,A,B,C,W[57],0x8F1BBCDC);
  SHA1_R2(C,D,E,A,B,W[58],0x8F1BBCDC);
  SHA1_R2(B,C,D,E,A,W[59],0x8F1BBCDC);

  /* Rounds 60-79: unrolled */
  SHA1_R1(A,B,C,D,E,W[60],0xCA62C1D6);
  SHA1_R1(E,A,B,C,D,W[61],0xCA62C1D6);
  SHA1_R1(D,E,A,B,C,W[62],0xCA62C1D6);
  SHA1_R1(C,D,E,A,B,W[63],0xCA62C1D6);
  SHA1_R1(B,C,D,E,A,W[64],0xCA62C1D6);
  SHA1_R1(A,B,C,D,E,W[65],0xCA62C1D6);
  SHA1_R1(E,A,B,C,D,W[66],0xCA62C1D6);
  SHA1_R1(D,E,A,B,C,W[67],0xCA62C1D6);
  SHA1_R1(C,D,E,A,B,W[68],0xCA62C1D6);
  SHA1_R1(B,C,D,E,A,W[69],0xCA62C1D6);
  SHA1_R1(A,B,C,D,E,W[70],0xCA62C1D6);
  SHA1_R1(E,A,B,C,D,W[71],0xCA62C1D6);
  SHA1_R1(D,E,A,B,C,W[72],0xCA62C1D6);
  SHA1_R1(C,D,E,A,B,W[73],0xCA62C1D6);
  SHA1_R1(B,C,D,E,A,W[74],0xCA62C1D6);
  SHA1_R1(A,B,C,D,E,W[75],0xCA62C1D6);
  SHA1_R1(E,A,B,C,D,W[76],0xCA62C1D6);
  SHA1_R1(D,E,A,B,C,W[77],0xCA62C1D6);
  SHA1_R1(C,D,E,A,B,W[78],0xCA62C1D6);
  SHA1_R1(B,C,D,E,A,W[79],0xCA62C1D6);

  hash[0] +=  A;
  hash[1] +=  B;
  hash[2] +=  C;
  hash[3] +=  D;
  hash[4] +=  E;
  return;
}

void sha256_md(unsigned char message[], int size, unsigned int hash[8]) {
  unsigned int bitlen = 8*size;
  hash[0] = 0x6A09E667;  
  hash[1] = 0xBB67AE85;
  hash[2] = 0x3C6EF372;  
  hash[3] = 0xA54FF53A;  
  hash[4] = 0x510E527F;
  hash[5] = 0x9B05688C;
  hash[6] = 0x1F83D9AB;
  hash[7] = 0x5BE0CD19;
  
  unsigned char msgTBH[64]; /* 64 BYTE msg to be hashed */
  unsigned char paddedMessage[64]; /* last msg block to be hashed*/
  int i;
  int Q= size/64;
  int R= size%64;
  unsigned char msg[R];
  memcpy(msg, &message[64*Q], R * sizeof(unsigned char));
  
  for (i=0; i<Q; i++) {
    memcpy(msgTBH, &message[64*i], 64 * sizeof(unsigned char));
    sha256_process(hash, msgTBH);
  }
  if (R>55) {
    memcpy(msgTBH, msg, R * sizeof(unsigned char));
    msgTBH[R]=0x80;
    for (i=R+1; i<64; i++) {
      msgTBH[i]=0x00;
    }
    sha256_process(hash, msgTBH);
    sha_msg_pad0(bitlen,paddedMessage);
  } else {
    sha_msg_pad(msg, R, bitlen, paddedMessage);
  }
 
  sha256_process(hash, paddedMessage);
  return;
}

void sha256_process(unsigned int hash[], unsigned char msg[]) {
  unsigned int W[64];
  int i;
  register unsigned int A, B, C, D, E, F, G, H;
  
  for(i = 0; i < 16; i++) {
    W[i] = (((unsigned) msg[i * 4]) << 24) |
      (((unsigned) msg[i * 4 + 1]) << 16) |
      (((unsigned) msg[i * 4 + 2]) << 8) | 
      (((unsigned) msg[i * 4 + 3]));
  }
  for(i = 16; i < 64; i++) {
    W[i] = sigma1(W[i-2])+W[i-7]+sigma0(W[i-15])+ W[i-16];
  }
  
  A = hash[0];
  B = hash[1];
  C = hash[2];
  D = hash[3];
  E = hash[4];
  F = hash[5];
  G = hash[6];
  H = hash[7];

  /* Fully unrolled 64 rounds */
  SHA256_ROUND(A,B,C,D,E,F,G,H,W[0],0x428a2f98);
  SHA256_ROUND(H,A,B,C,D,E,F,G,W[1],0x71374491);
  SHA256_ROUND(G,H,A,B,C,D,E,F,W[2],0xb5c0fbcf);
  SHA256_ROUND(F,G,H,A,B,C,D,E,W[3],0xe9b5dba5);
  SHA256_ROUND(E,F,G,H,A,B,C,D,W[4],0x3956c25b);
  SHA256_ROUND(D,E,F,G,H,A,B,C,W[5],0x59f111f1);
  SHA256_ROUND(C,D,E,F,G,H,A,B,W[6],0x923f82a4);
  SHA256_ROUND(B,C,D,E,F,G,H,A,W[7],0xab1c5ed5);
  SHA256_ROUND(A,B,C,D,E,F,G,H,W[8],0xd807aa98);
  SHA256_ROUND(H,A,B,C,D,E,F,G,W[9],0x12835b01);
  SHA256_ROUND(G,H,A,B,C,D,E,F,W[10],0x243185be);
  SHA256_ROUND(F,G,H,A,B,C,D,E,W[11],0x550c7dc3);
  SHA256_ROUND(E,F,G,H,A,B,C,D,W[12],0x72be5d74);
  SHA256_ROUND(D,E,F,G,H,A,B,C,W[13],0x80deb1fe);
  SHA256_ROUND(C,D,E,F,G,H,A,B,W[14],0x9bdc06a7);
  SHA256_ROUND(B,C,D,E,F,G,H,A,W[15],0xc19bf174);
  SHA256_ROUND(A,B,C,D,E,F,G,H,W[16],0xe49b69c1);
  SHA256_ROUND(H,A,B,C,D,E,F,G,W[17],0xefbe4786);
  SHA256_ROUND(G,H,A,B,C,D,E,F,W[18],0x0fc19dc6);
  SHA256_ROUND(F,G,H,A,B,C,D,E,W[19],0x240ca1cc);
  SHA256_ROUND(E,F,G,H,A,B,C,D,W[20],0x2de92c6f);
  SHA256_ROUND(D,E,F,G,H,A,B,C,W[21],0x4a7484aa);
  SHA256_ROUND(C,D,E,F,G,H,A,B,W[22],0x5cb0a9dc);
  SHA256_ROUND(B,C,D,E,F,G,H,A,W[23],0x76f988da);
  SHA256_ROUND(A,B,C,D,E,F,G,H,W[24],0x983e5152);
  SHA256_ROUND(H,A,B,C,D,E,F,G,W[25],0xa831c66d);
  SHA256_ROUND(G,H,A,B,C,D,E,F,W[26],0xb00327c8);
  SHA256_ROUND(F,G,H,A,B,C,D,E,W[27],0xbf597fc7);
  SHA256_ROUND(E,F,G,H,A,B,C,D,W[28],0xc6e00bf3);
  SHA256_ROUND(D,E,F,G,H,A,B,C,W[29],0xd5a79147);
  SHA256_ROUND(C,D,E,F,G,H,A,B,W[30],0x06ca6351);
  SHA256_ROUND(B,C,D,E,F,G,H,A,W[31],0x14292967);
  SHA256_ROUND(A,B,C,D,E,F,G,H,W[32],0x27b70a85);
  SHA256_ROUND(H,A,B,C,D,E,F,G,W[33],0x2e1b2138);
  SHA256_ROUND(G,H,A,B,C,D,E,F,W[34],0x4d2c6dfc);
  SHA256_ROUND(F,G,H,A,B,C,D,E,W[35],0x53380d13);
  SHA256_ROUND(E,F,G,H,A,B,C,D,W[36],0x650a7354);
  SHA256_ROUND(D,E,F,G,H,A,B,C,W[37],0x766a0abb);
  SHA256_ROUND(C,D,E,F,G,H,A,B,W[38],0x81c2c92e);
  SHA256_ROUND(B,C,D,E,F,G,H,A,W[39],0x92722c85);
  SHA256_ROUND(A,B,C,D,E,F,G,H,W[40],0xa2bfe8a1);
  SHA256_ROUND(H,A,B,C,D,E,F,G,W[41],0xa81a664b);
  SHA256_ROUND(G,H,A,B,C,D,E,F,W[42],0xc24b8b70);
  SHA256_ROUND(F,G,H,A,B,C,D,E,W[43],0xc76c51a3);
  SHA256_ROUND(E,F,G,H,A,B,C,D,W[44],0xd192e819);
  SHA256_ROUND(D,E,F,G,H,A,B,C,W[45],0xd6990624);
  SHA256_ROUND(C,D,E,F,G,H,A,B,W[46],0xf40e3585);
  SHA256_ROUND(B,C,D,E,F,G,H,A,W[47],0x106aa070);
  SHA256_ROUND(A,B,C,D,E,F,G,H,W[48],0x19a4c116);
  SHA256_ROUND(H,A,B,C,D,E,F,G,W[49],0x1e376c08);
  SHA256_ROUND(G,H,A,B,C,D,E,F,W[50],0x2748774c);
  SHA256_ROUND(F,G,H,A,B,C,D,E,W[51],0x34b0bcb5);
  SHA256_ROUND(E,F,G,H,A,B,C,D,W[52],0x391c0cb3);
  SHA256_ROUND(D,E,F,G,H,A,B,C,W[53],0x4ed8aa4a);
  SHA256_ROUND(C,D,E,F,G,H,A,B,W[54],0x5b9cca4f);
  SHA256_ROUND(B,C,D,E,F,G,H,A,W[55],0x682e6ff3);
  SHA256_ROUND(A,B,C,D,E,F,G,H,W[56],0x748f82ee);
  SHA256_ROUND(H,A,B,C,D,E,F,G,W[57],0x78a5636f);
  SHA256_ROUND(G,H,A,B,C,D,E,F,W[58],0x84c87814);
  SHA256_ROUND(F,G,H,A,B,C,D,E,W[59],0x8cc70208);
  SHA256_ROUND(E,F,G,H,A,B,C,D,W[60],0x90befffa);
  SHA256_ROUND(D,E,F,G,H,A,B,C,W[61],0xa4506ceb);
  SHA256_ROUND(C,D,E,F,G,H,A,B,W[62],0xbef9a3f7);
  SHA256_ROUND(B,C,D,E,F,G,H,A,W[63],0xc67178f2);
  
  hash[0] +=A;
  hash[1] +=B;
  hash[2] +=C;
  hash[3] +=D;
  hash[4] +=E;
  hash[5] +=F;
  hash[6] +=G;
  hash[7] +=H;
  return;
}


void sha512_msg_pad(unsigned char message[], int size, unsigned int bitlen, unsigned char paddedmsg[]) {
  int i;
  for (i=0; i<size; i++) {
    paddedmsg[i]=message[i];
  }
  paddedmsg[size]= 0x80;
  for (i=size+1; i<128; i++) {
    paddedmsg[i]=0x00;
  }
  paddedmsg[127] = bitlen;
  paddedmsg[126] = bitlen >> 8;
  paddedmsg[125] = bitlen >> 16;
  paddedmsg[124] = bitlen >> 24;
  return;
}

void sha512_msg_pad0(unsigned int bitlen, unsigned char paddedmsg[]) {
  int i;
  for (i=0; i<128; i++) {
    paddedmsg[i]=0x00;
  }
  paddedmsg[127] = bitlen;
  paddedmsg[126] = bitlen >> 8;
  paddedmsg[125] = bitlen >> 16;
  paddedmsg[124] = bitlen >> 24;
  return;
}


void sha512_md(unsigned char message[], int size, unsigned long hash[8]) {
  unsigned int bitlen = 8*size;
  hash[0] = 0x6a09e667f3bcc908;
  hash[1] = 0xbb67ae8584caa73b;
  hash[2] = 0x3c6ef372fe94f82b;
  hash[3] = 0xa54ff53a5f1d36f1;
  hash[4] = 0x510e527fade682d1;
  hash[5] = 0x9b05688c2b3e6c1f;
  hash[6] = 0x1f83d9abfb41bd6b;
  hash[7] = 0x5be0cd19137e2179;
  
  unsigned char msgTBH[128]; /* 128 BYTE msg to be hashed */
  unsigned char paddedMessage[128]; /* last msg block to be hashed*/
  
  int Q= size/128;
  int R= size%128;
  unsigned char msg[R];
  memcpy(msg, &message[128*Q], R * sizeof(unsigned char));
  int i;
  for (i=0; i<Q; i++) {
    memcpy(msgTBH, &message[128*i], 128 * sizeof(unsigned char));
    sha512_process(hash, msgTBH);
  }
  if (R>111) {
    memcpy(msgTBH, msg, R * sizeof(unsigned char));
    msgTBH[R]=0x80;
    for (i=R+1; i<128; i++) {
      msgTBH[i]=0x00;
    }
    sha512_process(hash, msgTBH);
    sha512_msg_pad0(bitlen,paddedMessage);
  } else {
    sha512_msg_pad(msg, R, bitlen, paddedMessage);
  }
 
  sha512_process(hash, paddedMessage);
  return;
}

void sha512_process(unsigned long hash[], unsigned char msg[]) {
  int i;
  unsigned long W[80];
  register unsigned long A, B, C, D, E, F, G, H;
  
  for(i = 0; i < 16; i++) {
    W[i] = (((unsigned long) msg[i * 8])<< 56) |
      (((unsigned long) msg[i * 8 + 1]) << 48) |
      (((unsigned long) msg[i * 8 + 2]) << 40) | 
      (((unsigned long) msg[i * 8 + 3]) << 32) |
      (((unsigned long) msg[i * 8 + 4]) << 24) |
      (((unsigned long) msg[i * 8 + 5]) << 16) | 
      (((unsigned long) msg[i * 8 + 6]) << 8)  |
      (((unsigned long) msg[i * 8 + 7]));
  }
  for(i = 16; i < 80; i++) {
    W[i] = sigma5121(W[i-2])+W[i-7]+sigma5120(W[i-15])+ W[i-16];
  }
  
  A = hash[0];
  B = hash[1];
  C = hash[2];
  D = hash[3];
  E = hash[4];
  F = hash[5];
  G = hash[6];
  H = hash[7];

  /* Fully unrolled 80 rounds */
  SHA512_ROUND(A,B,C,D,E,F,G,H,W[0],0x428a2f98d728ae22);
  SHA512_ROUND(H,A,B,C,D,E,F,G,W[1],0x7137449123ef65cd);
  SHA512_ROUND(G,H,A,B,C,D,E,F,W[2],0xb5c0fbcfec4d3b2f);
  SHA512_ROUND(F,G,H,A,B,C,D,E,W[3],0xe9b5dba58189dbbc);
  SHA512_ROUND(E,F,G,H,A,B,C,D,W[4],0x3956c25bf348b538);
  SHA512_ROUND(D,E,F,G,H,A,B,C,W[5],0x59f111f1b605d019);
  SHA512_ROUND(C,D,E,F,G,H,A,B,W[6],0x923f82a4af194f9b);
  SHA512_ROUND(B,C,D,E,F,G,H,A,W[7],0xab1c5ed5da6d8118);
  SHA512_ROUND(A,B,C,D,E,F,G,H,W[8],0xd807aa98a3030242);
  SHA512_ROUND(H,A,B,C,D,E,F,G,W[9],0x12835b0145706fbe);
  SHA512_ROUND(G,H,A,B,C,D,E,F,W[10],0x243185be4ee4b28c);
  SHA512_ROUND(F,G,H,A,B,C,D,E,W[11],0x550c7dc3d5ffb4e2);
  SHA512_ROUND(E,F,G,H,A,B,C,D,W[12],0x72be5d74f27b896f);
  SHA512_ROUND(D,E,F,G,H,A,B,C,W[13],0x80deb1fe3b1696b1);
  SHA512_ROUND(C,D,E,F,G,H,A,B,W[14],0x9bdc06a725c71235);
  SHA512_ROUND(B,C,D,E,F,G,H,A,W[15],0xc19bf174cf692694);
  SHA512_ROUND(A,B,C,D,E,F,G,H,W[16],0xe49b69c19ef14ad2);
  SHA512_ROUND(H,A,B,C,D,E,F,G,W[17],0xefbe4786384f25e3);
  SHA512_ROUND(G,H,A,B,C,D,E,F,W[18],0x0fc19dc68b8cd5b5);
  SHA512_ROUND(F,G,H,A,B,C,D,E,W[19],0x240ca1cc77ac9c65);
  SHA512_ROUND(E,F,G,H,A,B,C,D,W[20],0x2de92c6f592b0275);
  SHA512_ROUND(D,E,F,G,H,A,B,C,W[21],0x4a7484aa6ea6e483);
  SHA512_ROUND(C,D,E,F,G,H,A,B,W[22],0x5cb0a9dcbd41fbd4);
  SHA512_ROUND(B,C,D,E,F,G,H,A,W[23],0x76f988da831153b5);
  SHA512_ROUND(A,B,C,D,E,F,G,H,W[24],0x983e5152ee66dfab);
  SHA512_ROUND(H,A,B,C,D,E,F,G,W[25],0xa831c66d2db43210);
  SHA512_ROUND(G,H,A,B,C,D,E,F,W[26],0xb00327c898fb213f);
  SHA512_ROUND(F,G,H,A,B,C,D,E,W[27],0xbf597fc7beef0ee4);
  SHA512_ROUND(E,F,G,H,A,B,C,D,W[28],0xc6e00bf33da88fc2);
  SHA512_ROUND(D,E,F,G,H,A,B,C,W[29],0xd5a79147930aa725);
  SHA512_ROUND(C,D,E,F,G,H,A,B,W[30],0x06ca6351e003826f);
  SHA512_ROUND(B,C,D,E,F,G,H,A,W[31],0x142929670a0e6e70);
  SHA512_ROUND(A,B,C,D,E,F,G,H,W[32],0x27b70a8546d22ffc);
  SHA512_ROUND(H,A,B,C,D,E,F,G,W[33],0x2e1b21385c26c926);
  SHA512_ROUND(G,H,A,B,C,D,E,F,W[34],0x4d2c6dfc5ac42aed);
  SHA512_ROUND(F,G,H,A,B,C,D,E,W[35],0x53380d139d95b3df);
  SHA512_ROUND(E,F,G,H,A,B,C,D,W[36],0x650a73548baf63de);
  SHA512_ROUND(D,E,F,G,H,A,B,C,W[37],0x766a0abb3c77b2a8);
  SHA512_ROUND(C,D,E,F,G,H,A,B,W[38],0x81c2c92e47edaee6);
  SHA512_ROUND(B,C,D,E,F,G,H,A,W[39],0x92722c851482353b);
  SHA512_ROUND(A,B,C,D,E,F,G,H,W[40],0xa2bfe8a14cf10364);
  SHA512_ROUND(H,A,B,C,D,E,F,G,W[41],0xa81a664bbc423001);
  SHA512_ROUND(G,H,A,B,C,D,E,F,W[42],0xc24b8b70d0f89791);
  SHA512_ROUND(F,G,H,A,B,C,D,E,W[43],0xc76c51a30654be30);
  SHA512_ROUND(E,F,G,H,A,B,C,D,W[44],0xd192e819d6ef5218);
  SHA512_ROUND(D,E,F,G,H,A,B,C,W[45],0xd69906245565a910);
  SHA512_ROUND(C,D,E,F,G,H,A,B,W[46],0xf40e35855771202a);
  SHA512_ROUND(B,C,D,E,F,G,H,A,W[47],0x106aa07032bbd1b8);
  SHA512_ROUND(A,B,C,D,E,F,G,H,W[48],0x19a4c116b8d2d0c8);
  SHA512_ROUND(H,A,B,C,D,E,F,G,W[49],0x1e376c085141ab53);
  SHA512_ROUND(G,H,A,B,C,D,E,F,W[50],0x2748774cdf8eeb99);
  SHA512_ROUND(F,G,H,A,B,C,D,E,W[51],0x34b0bcb5e19b48a8);
  SHA512_ROUND(E,F,G,H,A,B,C,D,W[52],0x391c0cb3c5c95a63);
  SHA512_ROUND(D,E,F,G,H,A,B,C,W[53],0x4ed8aa4ae3418acb);
  SHA512_ROUND(C,D,E,F,G,H,A,B,W[54],0x5b9cca4f7763e373);
  SHA512_ROUND(B,C,D,E,F,G,H,A,W[55],0x682e6ff3d6b2b8a3);
  SHA512_ROUND(A,B,C,D,E,F,G,H,W[56],0x748f82ee5defb2fc);
  SHA512_ROUND(H,A,B,C,D,E,F,G,W[57],0x78a5636f43172f60);
  SHA512_ROUND(G,H,A,B,C,D,E,F,W[58],0x84c87814a1f0ab72);
  SHA512_ROUND(F,G,H,A,B,C,D,E,W[59],0x8cc702081a6439ec);
  SHA512_ROUND(E,F,G,H,A,B,C,D,W[60],0x90befffa23631e28);
  SHA512_ROUND(D,E,F,G,H,A,B,C,W[61],0xa4506cebde82bde9);
  SHA512_ROUND(C,D,E,F,G,H,A,B,W[62],0xbef9a3f7b2c67915);
  SHA512_ROUND(B,C,D,E,F,G,H,A,W[63],0xc67178f2e372532b);
  SHA512_ROUND(A,B,C,D,E,F,G,H,W[64],0xca273eceea26619c);
  SHA512_ROUND(H,A,B,C,D,E,F,G,W[65],0xd186b8c721c0c207);
  SHA512_ROUND(G,H,A,B,C,D,E,F,W[66],0xeada7dd6cde0eb1e);
  SHA512_ROUND(F,G,H,A,B,C,D,E,W[67],0xf57d4f7fee6ed178);
  SHA512_ROUND(E,F,G,H,A,B,C,D,W[68],0x06f067aa72176fba);
  SHA512_ROUND(D,E,F,G,H,A,B,C,W[69],0x0a637dc5a2c898a6);
  SHA512_ROUND(C,D,E,F,G,H,A,B,W[70],0x113f9804bef90dae);
  SHA512_ROUND(B,C,D,E,F,G,H,A,W[71],0x1b710b35131c471b);
  SHA512_ROUND(A,B,C,D,E,F,G,H,W[72],0x28db77f523047d84);
  SHA512_ROUND(H,A,B,C,D,E,F,G,W[73],0x32caab7b40c72493);
  SHA512_ROUND(G,H,A,B,C,D,E,F,W[74],0x3c9ebe0a15c9bebc);
  SHA512_ROUND(F,G,H,A,B,C,D,E,W[75],0x431d67c49c100d4c);
  SHA512_ROUND(E,F,G,H,A,B,C,D,W[76],0x4cc5d4becb3e42b6);
  SHA512_ROUND(D,E,F,G,H,A,B,C,W[77],0x597f299cfc657e2a);
  SHA512_ROUND(C,D,E,F,G,H,A,B,W[78],0x5fcb6fab3ad6faec);
  SHA512_ROUND(B,C,D,E,F,G,H,A,W[79],0x6c44198c4a475817);
  
  hash[0] +=A;
  hash[1] +=B;
  hash[2] +=C;
  hash[3] +=D;
  hash[4] +=E;
  hash[5] +=F;
  hash[6] +=G;
  hash[7] +=H;
  return;
}


int testSHA(int shatype, int numT){
  //you should not make any changes to this function. Any modification to this function
  //is considered a violaiton of the academic integrity
  unsigned int hash1[5];
  unsigned int hash2[8];
  unsigned long hash3[8];
  int size=3, i;
  clock_t start, finish;
  double seconds;
  static unsigned char msg4[1000000];
  for (i=0; i<1000000; i++)  msg4[i]='a';
  size=1000000;
  
  if (shatype==1) {
    sha1_md(msg4, size, hash1);
    if ((hash1[0] !=0x34aa973c)||(hash1[1]!=0xd4c4daa4)||(hash1[2]!=0xf61eeb2b)
	||(hash1[3]!=0xdbad2731)||(hash1[4]!=0x6534016f)) {
      printf("SHA-1 failed\n");
      return 1;
    } else {
      start = clock();
      for (i=0;i<numT;i++) sha1_md(msg4, size, hash1);
      finish = clock();
      seconds = ((double)(finish - start))/CLOCKS_PER_SEC;
      printf("%f seconds for %d times of SHA-1\n",seconds,numT);
    }
  }
  
  if (shatype==2) {
    sha256_md(msg4, size,hash2);
    if ((hash2[0] != 0xcdc76e5c)||(hash2[1]!=0x9914fb92)||(hash2[2]!=0x81a1c7e2)
      ||(hash2[3]!=0x84d73e67)||(hash2[4]!=0xf1809a48)||(hash2[5]!=0xa497200e)
	||(hash2[6]!=0x046d39cc)||(hash2[7]!=0xc7112cd0)) {
      printf("SHA-1 failed\n");
      return 1;
    } else {
      start = clock();
      for (i=0;i<numT;i++) sha256_md(msg4, size,hash2);
      finish = clock();
      seconds = ((double)(finish - start))/CLOCKS_PER_SEC;
      printf("%f seconds for %d times of SHA-256\n",seconds,numT);
    }
  }
  
  if (shatype==3) {
    sha512_md(msg4, size,hash3);
    if ((hash3[0] != 0xe718483d0ce76964)||(hash3[1]!=0x4e2e42c7bc15b463)||(hash3[2]!=0x8e1f98b13b204428)
      ||(hash3[3]!=0x5632a803afa973eb)||(hash3[4]!=0xde0ff244877ea60a)||(hash3[5]!=0x4cb0432ce577c31b)
	||(hash3[6]!=0xeb009c5c2c49aa2e)||(hash3[7]!=0x4eadb217ad8cc09b)) {
      printf("SHA-1 failed\n");
      return 1;
    } else {
      start = clock();
      for (i=0;i<numT;i++) sha512_md(msg4, size,hash3);
      finish = clock();
      seconds = ((double)(finish - start))/CLOCKS_PER_SEC;
      printf("%f seconds for %d times of SHA-512\n",seconds,numT);
    }
  }
  return 0;
}