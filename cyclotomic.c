#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <stdint.h>
#include "flint.h"
#include "ulong_extras.h"

/* 
   Code for evaluating s, t as follows:

   Let p be prime, k even. 
   
   Then

   s = sum_{a=1}^{(p-1)/2} a^(k-1) mod p^2

   t = sum_{a=1}^{(p-1)/2} a^(p+k-2) mod p^2

   We compute s/p and t/p.
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

mp_limb_t invert_half(mp_limb_t n)
{
   mp_limb_t norm, ninv;

   count_leading_zeros(norm, n);
   n <<= (norm - 32);

   ninv = (~(mp_limb_t) 0) - (n << 32);
   return ninv / n;
}

mp_limb_t divrem_preinv(mp_limb_t * q, mp_limb_t a, mp_limb_t n, mp_limb_t ninv)
{
    mp_limb_t q1, r;

    {
	     const mp_limb_t u1 = (a>>32);
        
        q1 = (ninv*u1 + a)>>32;
        r = (a - q1*n);

        if (r < n) 
        {
           *q = q1;
           return r;
        } else
        {
           *q = q1 + 1;
           r = r - n;

           if (r < n)
              return r;
           else
           {
              *q = q1 + 2;
              return r - n;
           }
        }
   }
}

void calc1(ulong p, ulong k)
{
   ulong j, v;
   ulong pinv, normp, phinv, normhp, phnorm, p2, p2inv, p2norm, normp2;
   ulong g, gj, gk1, gk2, gpk2, gpk3, gjpk2, gjpk3;
   ulong u, k1p, k2p, gjk1, gjk2, ak1, apk2, diff, diff2, s, t, r;
   ulong ord2, to2, twok1, twopk2, twok2, twopk3;
   ulong _gjk1, _gjpk2, _gjk2, _gjpk3, _gj, u2, r2;
   int negate;
   n_factor_t fac;
   
   count_leading_zeros(normp, p);
   pinv = n_preinvert_limb(p);
   normhp = normp - 32;
   phinv = invert_half(p); /* precomputed inverse using Moller-Granlund */ 
   phnorm = (p << normhp); /* normalised version of p for our fast mulmod2_preinv */
   
   p2 = p*p; /* p2 = p^2 */  
   count_leading_zeros(normp2, p2);
   p2inv = n_preinvert_limb(p2); /* precomputed inverse using Moller-Granlund */ 
   p2norm = (p2 << normp2); /* normalised version of p^2 for our fast mulmod2_preinv */
   
   /* Step 1: compute g = primitive root mod p */
   
   g = n_primitive_root_prime(p);

   /* Step 1a: find the order of 2 mod p. We know it will be a factor
               d of p-1. Let to2 = (p - 1)/d. We then have that g^to2
               is a power of 2 mod p. */

   ord2 = p - 1;
   n_factor_init(&fac);
   n_factor(&fac, ord2, 1);

   for (j = 0; j < fac.num; j++) /* iterate over prime factors s of p - 1 */
   {
      for (v = 0; v < fac.exp[j]; v++) /* iterate over powers of s */
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

   /* 
      Step 2: compute k1p = (k-1)p mod p^2 
       and k2p = (p+k-2)p = (k-2)p mod p^2
   */
   
   k1p = ((k - 1)*p)<<normp2;
   k2p = ((k - 2)*p)<<normp2;
   
   /* 
      Step 3: compute gk1 = g^(k-1) mod p^2 
               and gpk2 = g^(p+k-2) mod p^2
   */
   
   gk1 = n_powmod2_preinv(g, k - 1, p2, p2inv)<<normp2;
   gpk2 = n_powmod2_preinv(g, p + k - 2, p2, p2inv)<<normp2;
   
   twok1 = n_powmod2_preinv(2, k - 1, p2, p2inv)<<normp2;
   twopk2 = n_powmod2_preinv(2, p + k - 2, p2, p2inv)<<normp2;

   /* 
      Step 4: compute gk2 = g^(k-2) mod p^2 
                 and gpk3 = g^(p+k-3) mod p^2 
   */
   
   gk2 = n_powmod2_preinv(g, k - 2, p2, p2inv)<<normp2;
   gpk3 = n_powmod2_preinv(g, p + k - 3, p2, p2inv)<<normp2;
   
   twok2 = n_powmod2_preinv(2, k - 2, p2, p2inv)<<normp2;
   twopk3 = n_powmod2_preinv(2, p + k - 3, p2, p2inv)<<normp2;
   
   /* 
      Step 5: compute a^(k-1) mod p^2 by cycling through a = g^j mod p 
              if g^j = a + tp mod p^2 then 
              (g^j)^(k-1) = a^(k-1) + (k-1)pa^(k-2)t mod p^2
                          = a^(k-1) + ((g^j)^(k-2)t mod p)(k-1)p mod p^2

              if g^j = -a + tp mod p^2 then 
              (g^j)^(k-1) = -a^(k-1) + (k-1)pa^(k-2)t mod p^2
                          = -a^(k-1) + ((g^j)^(k-2)t mod p)(k-1)p mod p^2

              similarly for a^(p+k-2)
   */

   g<<=normp2;

   gjk1 = 1UL<<normp2;
   gjpk2 = 1UL<<normp2;
   gjk2 = k1p;
   gjpk3 = k2p;
   gj = 1UL<<normp2;
   s = 0;
   t = 0;

   for (j = 1; j <= to2; j++)
   {
      /* 
         Step 5a: set gjk1 = (g^j)^(k-1) mod p^2 
                  and gjpk2 = (g^j)^(p+k-2) mod p^2
      */
      
      mulmod_preinv(gjk1, gjk1, gk1, p2norm, p2inv, normp2);
      mulmod_preinv(gjpk2, gjpk2, gpk2, p2norm, p2inv, normp2);
      
      /* 
         Step 5b: set gjk2 = (g^j)^(k-2)*(k-1)p mod p^2 
                  and gjpk3 = (g^j)^(p+k-3)*(k-2)p mod p^2
      */
      
      mulmod_preinv(gjk2, gjk2, gk2, p2norm, p2inv, normp2);
      mulmod_preinv(gjpk3, gjpk3, gpk3, p2norm, p2inv, normp2);

      /* Step 5c: set gj = (g^j) mod p^2 */
 
      mulmod_preinv(gj, gj, g, p2norm, p2inv, normp2);

      /* Step 5d : set u = gj / p, r = gj % p */

      r = divrem_preinv(&u, gj>>(normp2 - normhp), phnorm, phinv)>>normhp;

      /* Step 5e: deal with g^j mod p > (p-1)/2 */

      negate = 0;
      if (r > (p-1)/2)
      {
         u2 = u + 1; /* this value needs to be correct mod p, but is used mod p^2 
                        so no need to reduce */
         negate = 1; 
      } else
         u2 = u;

      /* 
         Step 5f: set diff = (k-1)pa^(k-2)u mod p^2 
                  and diff2 = (k-2)pa^(p+k-3)u mod p^2
      */

      mulmod_preinv(diff, gjk2, u2<<normp2, p2norm, p2inv, normp2);
      mulmod_preinv(diff2, gjpk3, u2<<normp2, p2norm, p2inv, normp2);

      /* 
         Step 5g: set ak1 = (-1)^negate * a^(k-1) mod p^2 
                  and apk2 = (-1)^negate * a^(p+k-2) mod p^2
      */

      ak1 = n_submod(gjk1, diff, p2norm);
      apk2 = n_submod(gjpk2, diff2, p2norm);

      /* inner loop: switch to powers of 2 instead of powers of g, now
         that we know g^j is a power of 2 mod p */

      _gjk1 = gjk1;
      _gjpk2 = gjpk2;

      _gjk2 = gjk2;
      _gjpk3 = gjpk3;

      _gj = gj;

      for (v = 0; v < ord2; v++)
      {
         /* Step 5h: add a^(k-1) mod p^2 to sum */

         if (negate)
         {
            s = n_submod(s, ak1, p2norm);
            t = n_submod(t, apk2, p2norm);
         } else
         {
            s = n_addmod(s, ak1, p2norm);
            t = n_addmod(t, apk2, p2norm);
         }

         /* 
            Step 5i: set _gjk1 = (g^j)^(k-1) mod p^2 
                     and _gjpk2 = (g^j)^(p+k-2) mod p^2
         */
      
         mulmod_preinv(_gjk1, _gjk1, twok1, p2norm, p2inv, normp2);
         mulmod_preinv(_gjpk2, _gjpk2, twopk2, p2norm, p2inv, normp2);

         /* 
            Step 5j: set gjk2 = (g^j)^(k-2)*(k-1)p mod p^2 
                  and gjpk3 = (g^j)^(p+k-3)*(k-2)p mod p^2
         */
      
         mulmod_preinv(_gjk2, _gjk2, twok2, p2norm, p2inv, normp2);
         mulmod_preinv(_gjpk3, _gjpk3, twopk3, p2norm, p2inv, normp2);

         /* Step 5k: set _gj = (g^j) mod p^2 */
 
         _gj = n_addmod(_gj, _gj, p2norm);

         /* Step 5l : set u2 = _gj / p, r = _gj % p */

         u = n_addmod(u, u, p);
         r2 = n_addmod(r, r, p);

         if (r2 < r)
            u++; /* this value needs to be correct mod p, but is used 
                                   mod p^2 so no need to reduce */
         r = r2;

         /* Step 5m: deal with g^j mod p > (p-1)/2 */

         negate = 0;
         if (r > (p-1)/2)
         {
            u2 = u + 1; /* this value needs to be correct mod p, but is used mod p^2 
                           so no need to reduce */
            negate = 1;
         } else
            u2 = u;

         /* 
            Step 5n: set diff = (k-1)pa^(k-2)u mod p^2 
                  and diff2 = (k-2)pa^(p+k-3)u mod p^2
         */

         mulmod_preinv(diff, _gjk2, u2<<normp2, p2norm, p2inv, normp2);
         mulmod_preinv(diff2, _gjpk3, u2<<normp2, p2norm, p2inv, normp2);

         /* 
            Step 5o: set ak1 = (-1)^negate * a^(k-1) mod p^2 
                  and apk2 = (-1)^negate * a^(p+k-2) mod p^2
         */

         ak1 = n_submod(_gjk1, diff, p2norm);
         apk2 = n_submod(_gjpk2, diff2, p2norm);
      }
   }
      
   /* Step 6: s = s/p, t = t/p */

   s = (s>>normp2) / p;
   t = (t>>normp2) / p;
   
   flint_printf(" %wu:%wu,%wu", k, s, t);
}

int main(void)
{
   ulong p;
   ulong k; 
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
         k = atol(pos);

         calc1(p, k);
         
         pos += strspn(pos, "0123456789"); /* jump past k and spaces */
         pos += strspn(pos, " \t");
      }
   
      flint_printf("\n");
   }

   free(buffer);

   return 0;
}
