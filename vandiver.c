#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include "flint.h"
#include "ulong_extras.h"

/* 
   Code for evaluating V as follows:

   Let q be the smallest prime = 1 mod p. 
   
   Then

   V = (\prod_{a=1}^{(p-1)/2} (w^a - w^{-a})^{a^{p-1-k}})^m  mod q,

   where m = (q-1)/p,  w = 2^{m/2} mod q
*/

#define mulmod_preinv(r, a1, b, n, ninv, norm)          \
   do {                                                 \
      mp_limb_t __q0, __q1, __s, __phi, __plo;          \
      __s = ((a1) >> (norm));                           \
      umul_ppmm(__phi, __plo, __s, b);                  \
      umul_ppmm(__q1, __q0, ninv, __phi);               \
      add_ssaaaa(__q1, __q0, __q1, __q0, __phi, __plo); \
      (r) = (__plo - (__q1 + 1) * (n));                 \
      if ((r) >= __q0)                                  \
         (r) += (n);                                    \
      if ((r) >= (n)) (r) -= (n);                       \
   } while (0)

#define powmod_ui_preinv(x, r, e, n, ninv, norm)                      \
   do {                                                               \
      mp_limb_t __a = (r);                                            \
      mp_limb_t __exp = (e);                                          \
      while (((__exp) & 1) == 0) {                                    \
         mulmod_preinv(__a, __a, __a, n, ninv, norm);                 \
         (__exp) >>= 1;                                               \
      }                                                               \
      (x) = __a;                                                      \
      while ((__exp) >>= 1) {                                         \
         mulmod_preinv(__a, __a, __a, n, ninv, norm);                 \
         if ((__exp) & 1) mulmod_preinv(x, x, __a, n, ninv, norm);    \
      }                                                               \
   } while (0)

void calc1(ulong p, ulong k1)
{
   ulong j, k;
   ulong m, q, qinv, q2, qinv2, w, pinv, g, wi;
   ulong ap1, _ap1, V1, b1, c1, d1;
   ulong wgj, wgji, _wgj, _wgji, gpk1, norm, normp, p2, pinv2;
   ulong ord2, to2, twopk1;
   n_factor_t fac;

   ulong * Pb1 = malloc(sizeof(ulong)*1024);
   ulong * Pc1 = malloc(sizeof(ulong)*1024);
   ulong * Pd1 = malloc(sizeof(ulong)*2048);

   count_leading_zeros(normp, p);
   
   pinv = n_preinvert_limb(p); /* precomputed inverse using Moller-Granlund */
   
   p2 = (p << normp); /* normalised version of q for our fast mulmod2_preinv */
   pinv2 = n_preinvert_limb(p2);

   /* Step 1: Compute q = smallest prime with q = 1 mod p */

   q = p + 1; /* start with p + 1 */

   while (!n_is_prime(q))
      q += p;

   count_leading_zeros(norm, q);

   qinv = n_preinvert_limb(q); /* precomputed inverse using Moller-Granlund */

   q2 = (q<<norm); /* normalised version of q for our fast mulmod2_preinv */
   qinv2 = n_preinvert_limb(q2);

   /* Step 2: compute m = (q - 1)/p */

   m = (q - 1)/p;

   assert(p*m == q - 1);
   assert((m%2) == 0);

   /* Step 3: compute w = 2^(m/2) mod q */
   
   w = n_powmod2_preinv(2, m/2, q, qinv);

   assert(w < q);
   assert(n_powmod2_preinv(w, 2*p, q, qinv) == 1);

   /* Step 4: compute g = primitive root mod p */
   
   g = n_primitive_root_prime(p);
   
   /* Step 5: compute wi = w^(-1) mod q */
   
   wi = n_invmod(w, q);
   
   /* Step 6: initialise bins for accumulation */

   for (j = 0; j < 1024; j++) {
      Pb1[j] = (UWORD(1)<<norm);
      Pc1[j] = (UWORD(1)<<norm);
   }

   for (j = 0; j < 2048; j++) {
      Pd1[j] = (UWORD(1)<<norm);
   }

   /* Step 7: find the order of 2 mod p. We know it will be a factor
              d of p-1. Let to2 = (p - 1)/d. We then have that g^to2
              is a power of 2 mod p. */

   ord2 = p - 1;
   n_factor_init(&fac);
   n_factor(&fac, ord2, 1);

   for (j = 0; j < fac.num; j++) /* iterate over prime factors s of p - 1 */
   {
      for (k = 0; k < fac.exp[j]; k++) /* iterate over powers of s */
      {
         if (n_powmod2_preinv(2, ord2/fac.p[j], p, pinv) == UWORD(1))
            ord2 /= fac.p[j];
      }
   }
   
   to2 = (p - 1)/ord2;

   /* We need (p - 1)/to2 to be even */
   if (ord2 & 1) {
      to2 /= 2;
   } else
      ord2 /= 2;

   /* Step 8a: compute gpk1 = g^(p - 1 - k1) mod p
           and compute twopk1 = 2^(p - 1 - k1) mod p */
   
   gpk1 = (n_powmod2_preinv(g, p - 1 - k1, p, pinv) << normp);
   twopk1 = (n_powmod2_preinv(2, p - 1 - k1, p, pinv) << normp);
   
   /* Step 9: compute a^(p - 1 - k) mod p by cycling through a = g^j */

   for (_ap1 = (UWORD(1)<<normp), j = 1, _wgj = (w<<norm), 
                 _wgji = (wi<<norm); j <= to2; j++) {
      ulong diff, ap1d;
      
      /* Step 9a: set ap = (g^(p - 1 - k))^j */

      _ap1 = n_mulmod_preinv(_ap1, gpk1, p2, pinv2, normp);

      /* Step 9b: set wgj = w^(g^j) and wgji = w^(-g^j) */

      if (g == 2) {
         mulmod_preinv(_wgj, _wgj, _wgj, q2, qinv2, norm);
         mulmod_preinv(_wgji, _wgji, _wgji, q2, qinv2, norm);
      } else {
         powmod_ui_preinv(_wgj, _wgj, g, q2, qinv2, norm);
         powmod_ui_preinv(_wgji, _wgji, g, q2, qinv2, norm);
      }
      
      ap1  = _ap1;
      wgj  = _wgj;
      wgji = _wgji;
      
      /* inner loop : switch to powers of 2 instead of powers of g, now
         that we know g^j is a power of 2 mod p */
      
      for (k = 0; k < ord2; k++)
      {
         /* Step 9c: compute b1, c1, d1 s.t. ap1 = b1 + c1*2^10 + d1*2^20 */

         ap1d = (ap1 >> normp);

         b1 = (ap1d & UWORD(1023));
         c1 = ((ap1d >> 10) & UWORD(1023));
         d1 = (ap1d >> 20);

         /* Step 9e: compute diff = w^a - w^(-a) (up to sign but final power m is even) */
 
         diff = n_submod(wgj, wgji, q2);

         /* Step 9f: accumulate product of (w^a - w^(-a)) in Pb1[b1], Pc1[c1], Pd1[d1] */

         Pb1[b1] = n_mulmod_preinv(Pb1[b1], diff, q2, qinv2, norm);
         Pc1[c1] = n_mulmod_preinv(Pc1[c1], diff, q2, qinv2, norm);
         Pd1[d1] = n_mulmod_preinv(Pd1[d1], diff, q2, qinv2, norm);
      
         /* Step 9h: set ap = (g^(p - 1 - k_))^j * (2^(p - 1 - k_))^k */

         ap1 = n_mulmod_preinv(ap1, twopk1, p2, pinv2, normp);

         /* Step 9b: set wgj = (w^(g^j))^(2^k) and wgji = (w^(-g^j))^(2^k) */

         mulmod_preinv(wgj, wgj, wgj, q2, qinv2, norm);
         mulmod_preinv(wgji, wgji, wgji, q2, qinv2, norm);
      }
   }

   /* Step 10: initialise V1 */
   
   V1 = 1;
   
   /* Step 11: multiply out all factors and accumulate in V1, V2 */
   
   for (j = 0; j < 1024; j++) {
      
      /* Step 11a: raise b1, c1 factors to powers */
    
      Pb1[j] = n_powmod2_preinv(Pb1[j]>>norm, j, q, qinv);
      Pc1[j] = n_powmod2_preinv(Pc1[j]>>norm, j<<10, q, qinv);
            
      /* Step 11c: accumulate b1, c1 powers in V1 */
    
      V1 = n_mulmod2_preinv(V1, Pb1[j], q, qinv);
      V1 = n_mulmod2_preinv(V1, Pc1[j], q, qinv);
   }

   for (j = 0; j < 2048; j++) {
      
      /* Step 11e: raise d1 factors to powers */
    
      Pd1[j] = n_powmod2_preinv(Pd1[j]>>norm, j<<20, q, qinv);

      /* Step 11g: accumulate d1 powers in V1 */
    
      V1 = n_mulmod2_preinv(V1, Pd1[j], q, qinv);

  }

   /* Step 12: raise V1 and V2 to power m */

   V1 = n_powmod2_preinv(V1, m, q, qinv);

   flint_printf(" %wu:%wu", k1, V1);
}

void calc2(ulong p, ulong k1, ulong k2)
{
   ulong j, k;
   ulong m, q, qinv, q2, qinv2, w, pinv, g, wi;
   ulong ap1, ap2, _ap1, _ap2, V1, V2, b1, c1, d1, b2, c2, d2;
   ulong wgj, wgji, _wgj, _wgji, gpk1, gpk2, norm, normp, p2, pinv2;
   ulong ord2, to2, twopk1, twopk2;
   n_factor_t fac;

   ulong * Pb1 = malloc(sizeof(ulong)*1024);
   ulong * Pc1 = malloc(sizeof(ulong)*1024);
   ulong * Pd1 = malloc(sizeof(ulong)*2048);

   ulong * Pb2 = malloc(sizeof(ulong)*1024);
   ulong * Pc2 = malloc(sizeof(ulong)*1024);
   ulong * Pd2 = malloc(sizeof(ulong)*2048);
   
   count_leading_zeros(normp, p);
   
   pinv = n_preinvert_limb(p); /* precomputed inverse using Moller-Granlund */
   
   p2 = (p << normp); /* normalised version of q for our fast mulmod2_preinv */
   pinv2 = n_preinvert_limb(p2);

   /* Step 1: Compute q = smallest prime with q = 1 mod p */

   q = p + 1; /* start with p + 1 */

   while (!n_is_prime(q))
      q += p;

   count_leading_zeros(norm, q);

   qinv = n_preinvert_limb(q); /* precomputed inverse using Moller-Granlund */

   q2 = (q<<norm); /* normalised version of q for our fast mulmod2_preinv */
   qinv2 = n_preinvert_limb(q2);

   /* Step 2: compute m = (q - 1)/p */

   m = (q - 1)/p;

   assert(p*m == q - 1);
   assert((m%2) == 0);

   /* Step 3: compute w = 2^(m/2) mod q */
   
   w = n_powmod2_preinv(2, m/2, q, qinv);

   assert(w < q);
   assert(n_powmod2_preinv(w, 2*p, q, qinv) == 1);

   /* Step 4: compute g = primitive root mod p */
   
   g = n_primitive_root_prime(p);
   
   /* Step 5: compute wi = w^(-1) mod q */
   
   wi = n_invmod(w, q);
   
   /* Step 6: initialise bins for accumulation */

   for (j = 0; j < 1024; j++) {
      Pb1[j] = (UWORD(1)<<norm);
      Pc1[j] = (UWORD(1)<<norm);
      
      Pb2[j] = (UWORD(1)<<norm);
      Pc2[j] = (UWORD(1)<<norm);
   }

   for (j = 0; j < 2048; j++) {
      Pd1[j] = (UWORD(1)<<norm);

      Pd2[j] = (UWORD(1)<<norm);
   }

   /* Step 7: find the order of 2 mod p. We know it will be a factor
              d of p-1. Let to2 = (p - 1)/d. We then have that g^to2
              is a power of 2 mod p. */

   ord2 = p - 1;
   n_factor_init(&fac);
   n_factor(&fac, ord2, 1);

   for (j = 0; j < fac.num; j++) /* iterate over prime factors s of p - 1 */
   {
      for (k = 0; k < fac.exp[j]; k++) /* iterate over powers of s */
      {
         if (n_powmod2_preinv(2, ord2/fac.p[j], p, pinv) == UWORD(1))
            ord2 /= fac.p[j];
      }
   }
   
   to2 = (p - 1)/ord2;

   /* We need (p - 1)/to2 to be even */
   if (ord2 & 1) {
      to2 /= 2;
   } else
      ord2 /= 2;

   /* Step 8a: compute gpk1 = g^(p - 1 - k1) mod p
           and compute twopk1 = 2^(p - 1 - k1) mod p */
   
   gpk1 = (n_powmod2_preinv(g, p - 1 - k1, p, pinv) << normp);
   twopk1 = (n_powmod2_preinv(2, p - 1 - k1, p, pinv) << normp);
   
   /* Step 8b: compute gpk2 = g^(p - 1 - k2) mod p
           and compute twopk2 = 2^(p - 1 - k2) mod p */

   gpk2 = (n_powmod2_preinv(g, p - 1 - k2, p, pinv) << normp);
   twopk2 = (n_powmod2_preinv(2, p - 1 - k2, p, pinv) << normp);

   /* Step 9: compute a^(p - 1 - k) mod p by cycling through a = g^j */

   for (_ap1 = (UWORD(1)<<normp), _ap2 = (UWORD(1)<<normp), j = 1, _wgj = (w<<norm), 
                 _wgji = (wi<<norm); j <= to2; j++) {
      ulong diff, ap1d, ap2d;
      
      /* Step 9a: set ap = (g^(p - 1 - k))^j */

      _ap1 = n_mulmod_preinv(_ap1, gpk1, p2, pinv2, normp);
      _ap2 = n_mulmod_preinv(_ap2, gpk2, p2, pinv2, normp);

      /* Step 9b: set wgj = w^(g^j) and wgji = w^(-g^j) */

      if (g == 2) {
         mulmod_preinv(_wgj, _wgj, _wgj, q2, qinv2, norm);
         mulmod_preinv(_wgji, _wgji, _wgji, q2, qinv2, norm);
      } else {
         powmod_ui_preinv(_wgj, _wgj, g, q2, qinv2, norm);
         powmod_ui_preinv(_wgji, _wgji, g, q2, qinv2, norm);
      }
      
      ap1  = _ap1;
      ap2  = _ap2;
      wgj  = _wgj;
      wgji = _wgji;
      
      /* inner loop : switch to powers of 2 instead of powers of g, now
         that we know g^j is a power of 2 mod p */
      
      for (k = 0; k < ord2; k++)
      {
         /* Step 9c: compute b1, c1, d1 s.t. ap1 = b1 + c1*2^10 + d1*2^20 */

         ap1d = (ap1 >> normp);
         ap2d = (ap2 >> normp);

         b1 = (ap1d & UWORD(1023));
         c1 = ((ap1d >> 10) & UWORD(1023));
         d1 = (ap1d >> 20);

         /* Step 9d: compute b2, c2, d2 s.t. ap2 = b2 + c2*2^10 + d2*2^20 */

         b2 = (ap2d & UWORD(1023));
         c2 = ((ap2d >> 10) & UWORD(1023));
         d2 = (ap2d >> 20);

         /* Step 9e: compute diff = w^a - w^(-a) (up to sign but final power m is even) */
 
         diff = n_submod(wgj, wgji, q2);

         /* Step 9f: accumulate product of (w^a - w^(-a)) in Pb1[b1], Pc1[c1], Pd1[d1] */

         Pb1[b1] = n_mulmod_preinv(Pb1[b1], diff, q2, qinv2, norm);
         Pc1[c1] = n_mulmod_preinv(Pc1[c1], diff, q2, qinv2, norm);
         Pd1[d1] = n_mulmod_preinv(Pd1[d1], diff, q2, qinv2, norm);

         /* Step 9g: accumulate product of (w^a - w^(-a)) in Pb2[b2], Pc2[c2], Pd2[d2] */
  
         Pb2[b2] = n_mulmod_preinv(Pb2[b2], diff, q2, qinv2, norm);
         Pc2[c2] = n_mulmod_preinv(Pc2[c2], diff, q2, qinv2, norm);
         Pd2[d2] = n_mulmod_preinv(Pd2[d2], diff, q2, qinv2, norm);
      
         /* Step 9h: set ap = (g^(p - 1 - k_))^j * (2^(p - 1 - k_))^k */

         ap1 = n_mulmod_preinv(ap1, twopk1, p2, pinv2, normp);
         ap2 = n_mulmod_preinv(ap2, twopk2, p2, pinv2, normp);

         /* Step 9b: set wgj = (w^(g^j))^(2^k) and wgji = (w^(-g^j))^(2^k) */

         mulmod_preinv(wgj, wgj, wgj, q2, qinv2, norm);
         mulmod_preinv(wgji, wgji, wgji, q2, qinv2, norm);
      }
   }

   /* Step 10: initialise V1, V2 */
   
   V1 = 1;
   V2 = 1;
   
   /* Step 11: multiply out all factors and accumulate in V1, V2 */
   
   for (j = 0; j < 1024; j++) {
      
      /* Step 11a: raise b1, c1 factors to powers */
    
      Pb1[j] = n_powmod2_preinv(Pb1[j]>>norm, j, q, qinv);
      Pc1[j] = n_powmod2_preinv(Pc1[j]>>norm, j<<10, q, qinv);
      
      /* Step 11b: raise b2, c2 factors to powers */
     
      Pb2[j] = n_powmod2_preinv(Pb2[j]>>norm, j, q, qinv);
      Pc2[j] = n_powmod2_preinv(Pc2[j]>>norm, j<<10, q, qinv);
      
      /* Step 11c: accumulate b1, c1 powers in V1 */
    
      V1 = n_mulmod2_preinv(V1, Pb1[j], q, qinv);
      V1 = n_mulmod2_preinv(V1, Pc1[j], q, qinv);
      
      /* Step 11d: accumulate b2, c2 powers in V1 */
    
      V2 = n_mulmod2_preinv(V2, Pb2[j], q, qinv);
      V2 = n_mulmod2_preinv(V2, Pc2[j], q, qinv);
   }

   for (j = 0; j < 2048; j++) {
      
      /* Step 11e: raise d1 factors to powers */
    
      Pd1[j] = n_powmod2_preinv(Pd1[j]>>norm, j<<20, q, qinv);

      /* Step 11f: raise d2 factors to powers */
     
      Pd2[j] = n_powmod2_preinv(Pd2[j]>>norm, j<<20, q, qinv);

      /* Step 11g: accumulate d1 powers in V1 */
    
      V1 = n_mulmod2_preinv(V1, Pd1[j], q, qinv);

      /* Step 11h: accumulate d2 powers in V1 */
    
      V2 = n_mulmod2_preinv(V2, Pd2[j], q, qinv);
   }

   /* Step 12: raise V1 and V2 to power m */

   V1 = n_powmod2_preinv(V1, m, q, qinv);
   V2 = n_powmod2_preinv(V2, m, q, qinv);

   flint_printf(" %wu:%wu %wu:%wu", k1, V1, k2, V2);
}

int main(void)
{
   ulong p;
   ulong k1; 
   ulong k2; 
   char * buffer = malloc(1000); /* buffer is realloc'd by getline */
   size_t len = 1000;
   char * pos;

   while (getline(&buffer, &len, stdin) != -1)
   {
      pos = buffer; /* may have been realloc'd */
      
      p = atol(pos); /* get p */

      if (p == 0) /* must be done, no valid p */
         return 0;

      flint_printf("%wu", p);

      pos += strspn(pos, "0123456789"); /* jump past p and spaces */
      pos += strspn(pos, " \t");

      while (pos[0] != '\n') /* may be no more k's */
      {
         k1 = atol(pos);

         pos += strspn(pos, "0123456789"); /* jump past k1 and spaces */
         pos += strspn(pos, " \t");

         if (pos[0] == '\n') /* only one more k */
            calc1(p, k1);
         else /* we have at least two k's */
         {
            k2 = atol(pos);

            pos += strspn(pos, "0123456789"); /* jump past k2 and spaces */
            pos += strspn(pos, " \t");

            calc2(p, k1, k2);
         }
      }
   
      flint_printf("\n");
   }

   free(buffer);

   return 0;
}
