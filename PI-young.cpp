# define fastcall __attribute__((optimize("-O3")))
# define IL __inline__ __attribute__((always_inline)) 

# define rep(_i,_s,_t) for(register int (_i)=(_s);(_i)<=(_t);++(_i))
# define dwn(_i,_s,_t) for(register int (_i)=(_s);(_i)>=(_t);--(_i))

# include <time.h>
# include <math.h>
# include <stdio.h>
# include <assert.h>
# include <iostream>
# include <string.h>
# include <algorithm>

# define int_log 31ll
# define max_used_len 16777216ll

fastcall IL int intSign(int x) { return x<0; }

fastcall IL double global_time() { return (double)clock() / CLOCKS_PER_SEC;	 }

fastcall IL int rand32() {
    return (int)(
            (rand() & 0xf) <<  0 |
            (rand() & 0xf) <<  8 |
            (rand() & 0xf) << 16 |
            (rand() & 0xf) << 24
        ) % 1000000000;
}

typedef double ld;

int bin[int_log+1];

struct pdd { int a,b,c; };

struct cpx {
	ld r, i; 
	fastcall IL cpx conj() {  return (cpx){r,-i}; }
};

cpx tf1[max_used_len],tf2[max_used_len];

fastcall cpx operator + (const cpx &a, const cpx &b) { return (cpx) { a.r + b.r, a.i + b.i}; }
fastcall cpx operator - (const cpx &a, const cpx &b) { return (cpx) { a.r - b.r, a.i - b.i}; }
fastcall cpx operator * (const cpx &a, const cpx &b) { return (cpx) { a.r*b.r - a.i*b.i, a.r*b.i + a.i*b.r}; }

fastcall cpx rand_cpx() { return (cpx){ (double)(rand32()%1000), (double)(rand32()%1000) }; }

const ld eps=1e-9;

namespace FFT {

	# define max_fft_log 23ll
	# define max_fft_len 8388608ll

	# define M_PI 3.14159265358979323846


	int *rev[max_fft_log+1];

	cpx *prw[max_fft_log+1],*prwi[max_fft_log+1];
	

	bool prepared_Rev[max_fft_log+1],prepared_W[max_fft_log+1];


	void prepareRev(int lg) {

		register int *tmp,len=bin[lg]; 

		rev[lg] = new int [len]; tmp=rev[lg]; tmp[0]=0;

		for(register int i=0;i<len;i++) tmp[i]=tmp[i>>1]>>1|((i&1)<<(lg-1));

		prepared_Rev[lg]=true; return;

	}

	void prepareWn(int lg,int p) {

		register cpx *pw,*pwi;
		
		prw  [lg] = new cpx [p]; pw  = prw  [lg];
		prwi [lg] = new cpx [p]; pwi = prwi [lg];

		register ld omega = M_PI/p,s,c;

		for(register int i=0;i<p;i++) {
			
			pw  [i] = (cpx){ c = cos(omega*i) ,   s = sin(omega*i) };
			pwi [i] = (cpx){ c				  , - s 			   };
			
		}

		prepared_W[lg] = true;

		return;
	}

	void fft_normal(cpx *a,int n, int flag) { // to compare
		for (int i = 0, j = 0; i < n; i++) {
			if (i > j) std::swap(a[i], a[j]);
			for (int t = n >> 1; (j ^= t) < t; t >>= 1);
		}
		int m = 2; cpx wn, w, t, u;
		for (; m <= n; m <<= 1) {
			wn = (cpx) {cos(2.0 * M_PI / m), flag * sin(2.0 * M_PI / m)}, w = (cpx) {1, 0};
			for (int i = 0; i < n; i += m, w = (cpx) {1, 0}) for (int k = 0, p = m >> 1; k < p; ++k, w = w * wn)
				t = w * a[i + k + p], u = a[i + k], a[i + k] = u + t, a[i + k + p] = u - t;
		}
		if (flag == -1) for (int i = 0; i < n; i++) a[i].r /= n;
		return;
	}

	void fft(register cpx *f,register int lg) {

		register int n= 1 << lg ;
		
		if(!prepared_Rev[lg])  prepareRev(lg);
		
		register int *tRev=rev[lg],i,m,log_m,k,p;
		
		register cpx *w,*f1,*f2,t;

		for(i=0;i<n;++i,++tRev) if(i<*tRev) 
			std::swap(f[i],f[*tRev]);

		for(m=2,log_m=1;m<=n;m<<=1,++log_m) {

			p=m>>1;

			if(!prepared_W[log_m]) prepareWn(log_m,p);

			for(i=0;i<n;i+=m) {

				w=prw[log_m];

				f1=f+i,f2=f+i+p;

				for(k=0;k<p;++k) {

					t=(*w)*(*f2);

					(*f2)=(*f1)-t;

					f1->r+=t.r;
					f1->i+=t.i;

					++f1,++f2,++w;
				}
			}
		}

		return;
	}

	void ifft(register cpx *f,register int lg) {

		register int n= 1 << lg ;
		
		register int *tRev=rev[lg],i,m,log_m,k,p;
		
		register cpx *w,*f1,*f2,t;

		for(i=0;i<n;++i,++tRev) if(i<*tRev) 
			std::swap(f[i],f[*tRev]);

		for(m=2,log_m=1;m<=n;m<<=1,++log_m) {

			p=m>>1;

			for(i=0;i<n;i+=m) {

				w=prwi[log_m];

				f1=f+i,f2=f+i+p;

				for(k=0;k<p;++k) {

					t=(*w)*(*f2);

					(*f2)=(*f1)-t;

					f1->r+=t.r;
					f1->i+=t.i;

					++f1,++f2,++w;
				}
			}
		}

		register ld img = 1.0 / n;

		for(i=0;i<n;i++) f[i].r*=img;

		return;
	}

	void Test() {

		double time_tot=0;

		register cpx *array = new cpx [max_fft_len];

		register ld *rp = new double [max_fft_len];

		for(int i=0;i<=max_fft_log;i++) {


			int len= 1 << i ;

			for(int j=0;j<len;j++) array[j]=(cpx) { rp[j] = (double)(rand32()%1000), 0 };

			double st=global_time();

			//fft_normal(array,len,+1);
			//fft_normal(array,len,-1);

			fft(array,i);
			ifft(array,i);

			printf("time used = %.3lf \n",global_time()-st);
			
			time_tot+=global_time()-st;

			for(int j=0;j<len;j++) assert( fabs(rp[j]-array[j].r) < eps);

			printf("accepted on len %d \n\n",len);

		}

		delete []array;
		
		printf("total time used = %.3lf \n",time_tot);

		return;

	}

}

namespace io {
    
    # define maxl 1048576ll
    
    char outbuf[maxl+5]; int Now;
 
    fastcall IL void putchar(char ch) {
        
		outbuf[Now++]=ch;
        
		if(Now==maxl)
			fwrite(outbuf,1,Now,stdout),Now=0;
        
		return;
    }
 
    fastcall IL void end() {
        
		if(Now)
            fwrite(outbuf,1,Now,stdout),Now=0;
        
		return;
    }
}

fastcall IL void putc(char c,bool dump_in_file) {
	
	if(dump_in_file) io::putchar(c);
	else putchar(c);
	
	return;
	
}

struct __float256 {
	
	int *array;  // digits , 9 digits in one position
	int dec,L;   // decimal digits , total digits  |  if number = 0 , L = 0
	bool sign;   /* if sign = false  , number >= 0
					   sign = true   , number <  0 */
					   
	inline __float256() { // Initialization , 0
		
		array = NULL;
		
		dec=L=sign=0;
		
		return;
		
	}
	
	fastcall IL void apply_memory(int len) {
		
		assert(array==NULL);
		
		array = new int [len]; return;
		
	}
	
	fastcall IL void destroy() {
		
		if(array!=NULL) delete []array;
		
		array = NULL;
		
		dec=L=sign=0;
		
		return;
	}
	
	fastcall IL void setDB(long double number) {
		
		destroy();
		
	//	std::cout<<number<<std::endl;
		
		if( fabs(number) < eps ) return;
		
		if(number<0) sign=true,number=-number;
		
		else sign=false;
		
		dec=1; // p1-> 10 -> 18, 1 -> 9
		
		// p2 -> 1 -> 9 , 10 -> 18
		
		int k=((long long)(number/1e9))%1000000000ll;
		
		apply_memory(L=3-(k==0));
		
		// 14159265358979323846
		
		array[0]=(int)((number - floor(number)+1e-12)*1e9);
		array[1]=((long long)(number))%1000000000ll;
		if(k) array[2]=k;
		
	//	printf("%d %d\n",array[0],array[1]);
		
	//	printf("%d dec = %d\n",L,dec);
		
		return;
		
	}
	
	fastcall IL void negate() {
		
		if(!L) return;
		
		sign^=1; return;
		
	}
	
	fastcall IL int IntegerLen() {
		
		return L-dec;
		
	}
	
	fastcall IL int at(int x) { // ->
		
		if(x>=L) return 0;
		
		return array[L-x-1];
	}
	
	fastcall IL int at2(int x) { // -<
		
		if(x>=L) return 0;
		
		return array[x];
		
	}
	
	fastcall IL int atdec(int x) {
		
		if(x>=dec) return 0;
		
		return array[dec-x-1];
		
	}
	
	fastcall IL int atInt(int x) {
		
		if(x>=L-dec) return 0;
		
		return array[dec+x];
		
	}
	
	void print_digit(int number,bool dump_in_file,bool first) {
		
		static int st[9];
		
		for(register int i=8;~i;--i) st[i]=number%10,number/=10;
		
		for(int i=0;i<9;i++) {
			
			if(first&&st[i]) first=false;
			
			if(!first) putc(st[i]+'0',dump_in_file);
			
		}
		
		if(first) putc('0',dump_in_file);
		
		return;
	
	}
	
	void print(register bool dump_in_file) {
			
		if(!L) putc('0',dump_in_file);
		else {
			
			if(sign) putc('-',dump_in_file);
			
			for(register int i=L-1;~i;--i) {
				
				print_digit(array[i],dump_in_file,i==(L-1));
				
				if(i&&i==dec) putc('.',dump_in_file);
				
			}
			
		}
		
		putc('\n',dump_in_file);

		return;

	}
	
};

fastcall IL pdd getDiv(int x) {
	
	register int a,b,c;
	
	a=x%1000,x/=1000;
	b=x%1000,x/=1000;
	c=x%1000;
	
	return (pdd){a,b,c};
	
}

fastcall IL int mergePdd(register int a,register int b,register int c) {
	return a+b*1000+c*1000000;
}

int cmp_unsigned(__float256 &x,__float256 &y) { // ignoring sign
	// 1 = (x<y) , 0 = (x=y) , -1 = (x>y)
	
	register int I1=x.IntegerLen(),I2=y.IntegerLen();
	
	if(I1!=I2) return I1<I2?1:-1;
	
	register int len = std::max(x.L,y.L);
	
	for(int i=0;i<len;i++) {
		
		I1=x.at(i),I2=y.at(i);
		
		if(I1!=I2) return I1<I2?1:-1;
	}	
	
	return 0; 
}

__float256 mul(__float256 &x,__float256 &y,int precision) {
	
	__float256 z;
	
	if(!x.L||!y.L) return z;
	
	z.sign=x.sign^y.sign;
	z.dec=x.dec+y.dec;
	
	register int len = std::max(x.L,y.L),tot=0,fft_len,lg,ndc=(x.dec+y.dec)*3;
	
	register pdd dx,dy;

	fft_len=1,lg=0;
	
	for(;fft_len<(x.L+y.L)*3;fft_len<<=1,++lg);
	
	for(register int i=0;i<len;i++) {
		
		dx=getDiv(x.at2(i)); dy=getDiv(y.at2(i));
		
		tf1[tot++]=(cpx){(ld)dx.a,(ld)dy.a};
		tf1[tot++]=(cpx){(ld)dx.b,(ld)dy.b};
		tf1[tot++]=(cpx){(ld)dx.c,(ld)dy.c};
		
	}
	
	while(tot!=fft_len) tf1[tot++]=(cpx){0,0};
	
	FFT::fft(tf1,lg);

	for(register int i=0,j;i<fft_len;i++) {
		
		j=(fft_len-1)&(fft_len-i);
		tf2[i]=(tf1[i]*tf1[i]-(tf1[j]*tf1[j]).conj())*(cpx){0,-0.25};
		
	}
	
	FFT::ifft(tf2,lg);
	
	int *temporary = new int[ len = (x.L+y.L+1)*3 ];
		
	long long inc=0;
	
	for(int i=0;i<len;i++) {
		
		temporary[i]=((long long)(tf2[i].r+0.5)+inc)%1000ll;
		inc=((long long)(tf2[i].r+0.5)+inc)/1000ll;
		
		// assert(temporary[i]>=0);
		
	}
	
	while((len/3)!=z.dec+1&&(!temporary[len-1])&&(!temporary[len-2])&&(!temporary[len-3])) len-=3;
	
	// last ndc = decimal
	
	int s=0;
	
	if(precision!=-1&&z.dec>precision){
		
		s=z.dec-precision;
		z.dec=precision;
		
	}
	
//	for(int i=0;i<len;i++) printf("%d \n",temporary[i]);
	
	z.apply_memory(z.L=(len-s*3)/3);
	
	len/=3;
	
	for(register int i=s;i<len;i++)
		z.array[i-s] = mergePdd(temporary[i*3],temporary[i*3+1],temporary[i*3+2]);
	
	return z;
}

void mul_to(__float256 &x,__float256 &y,int precision) {
	
	__float256 z=mul(x,y,precision);
	
	x.destroy(); x=z; return;
	
}

__float256 mul(__float256 &x,long long y) {

	__float256 z;
	
	if(!y||!x.L) return z;
	
	register long long inc=0;
	
	z.L=x.L+2; z.sign=x.sign^intSign(y);
	
	if(y<0) y=-y;
	
	z.array=new int[z.L+2];
	
	z.dec=x.dec;
	
	for(int i=0;i<x.L;i++) {
		
		z.array[i]=(inc+1ll*x.array[i]*y)%1000000000ll;
		inc=(inc+1ll*x.array[i]*y)/1000000000ll;
		
	}
	
	while(z.L!=z.dec+1&&!z.array[z.L-1]) --z.L;
	
	return z;
}

void mul_to(__float256 &x,long long y) {
	
	__float256 z=mul(x,y);
	
	x.destroy(); x=z; return;
}

__float256 add_unsigned(__float256 &x,__float256 &y) {
	
	__float256 z;
	
	z.sign=false;
	
	z.dec=std::max(x.dec,y.dec);
	
	z.L=z.dec+std::max(x.L-x.dec,y.L-y.dec)+1;
	
	z.array=new int [z.L];
	
	register long long inc=0;

	register int I1,I2;
	
	for(register int i=0;i<z.dec;i++) {
	
		I1=x.atdec(z.dec-i-1);
		I2=y.atdec(z.dec-i-1);
	
		z.array[i]=(I1+I2+inc)%1000000000ll;
		inc=(I1+I2+inc)/1000000000ll;
		
	}
	
	for(register int i=z.dec;i<z.L;i++) {
		
		I1=x.atInt(i-z.dec);
		I2=y.atInt(i-z.dec);
		
		z.array[i]=(I1+I2+inc)%1000000000ll;
		inc=(I1+I2+inc)/1000000000ll;
		
	}
	
	while(z.L!=z.dec+1&&!z.array[z.L-1]) --z.L;
	
	return z;
	
}

__float256 sub_unsigned(__float256 &x,__float256 &y) {
	
	// promise x >= y

	__float256 z;
	
	z.sign=false;
	
	z.dec=std::max(x.dec,y.dec);
	
	z.L=z.dec+std::max(x.L-x.dec,y.L-y.dec)+1;
	
	z.array=new int [z.L];
	
	register long long borrow=0;
	
	register int I1,I2;
	
	for(register int i=0;i<z.dec;i++) {
	
		I1=x.atdec(z.dec-i-1);
		I2=y.atdec(z.dec-i-1);
	
		z.array[i]=I1-I2+borrow;
		
		borrow=0;
		
		while(z.array[i]<0) {
			
			z.array[i]+=1000000000ll;
			--borrow;
			
		}
		
	}
	
	for(register int i=z.dec;i<z.L;i++) {
		
		I1=x.atInt(i-z.dec);
		I2=y.atInt(i-z.dec);
		
		z.array[i]=I1-I2+borrow;
		
		borrow=0;
		
		while(z.array[i]<0) {
			
			z.array[i]+=1000000000ll;
			--borrow;
			
		}
		
	}
	
	while(z.L!=z.dec+1&&!z.array[z.L-1]) --z.L;
	
	return z;
	
}

__float256 add(__float256 &x,__float256 &y) {
	
	__float256 z;
	
	if(x.sign==y.sign) {
		
		z=add_unsigned(x,y);
		
		z.sign=x.sign;
		
	} else {
		
		if(cmp_unsigned(x,y)<=0) { // |x| > =|y|
			
			z=sub_unsigned(x,y);
			z.sign=x.sign;
			
		} else {
			
			z=sub_unsigned(y,x); // |x| < |y|
			z.sign=y.sign;
			
		}
		
	}
	
	return z;
	
}

void add_to(__float256 &x,__float256 &y) {
	
	__float256 z; z=add(x,y);
	
	x.destroy(); x=z; return;
	
}

__float256 sub(__float256 &x,__float256 &y) {
	
	__float256 z;
	
	if(x.sign!=y.sign) {
		
		z=add_unsigned(x,y);
		
		z.sign=x.sign;
		
	} else {
		
		if(cmp_unsigned(x,y)<=0) { // |x| > =|y|
			
			z=sub_unsigned(x,y);
			z.sign=x.sign;
			
		} else {
			
			z=sub_unsigned(y,x); // |x| < |y|
			z.sign=x.sign^1;
			
		}
		
	}
	
	return z;
	
}

void sub_to(__float256 &x,__float256 &y) {
	
	__float256 z; z=sub(x,y);
	
	x.destroy(); x=z; return;
	
}

__float256 rcp(__float256 &x,int precision) {
	
	//  newton iteration :  r1 = r0 - (r0 * x - 1) * r0 
	
}

__float256 div(__float256 &x,__float256 &y) {
	
	
	
}

void div_to(__float256 &x,__float256 &y) {
	
	__float256 z; z = div(x,y);
	
	x.destroy(); x=z; return ;
	
}

void prepareUtility() {
	
	bin[0]=1;
	
	for(int i=1;i<=int_log;i++) bin[i]=1<<i;
	
	return;
}

void __float256_Test1() {
	
	__float256 a,c;
	
	// a.setDB(-3456789123456789.2);
	
	// a.print(0);
	
	a.setDB(2);
	
	double st=global_time();
	
	while(a.L*9<17000000) {
		
		mul_to(a,a,0);
		
		if(a.L<500) a.print(0),puts("");
		
		
	}
	
	printf("time used = %.2lf \n",global_time()-st);
	
	return;
	
}

void __float256_Test2() {
	
	__float256 a,b;
	
	a.setDB(15.3),b.setDB(-15.2);
	
	a.print(0),b.print(0);
	
	printf("%d \n",cmp_unsigned(a,b));
	
	return;
	
}

void __float256_Test3() {
	
	__float256 a;
	
	a.setDB(-0.3);
	
	a.print(0);
	
	mul_to(a,-9);
	
	a.print(0);
	
	return;
	
}

void __float256_Test4() {
	
	__float256 a,b,c;
	
	a.setDB(-200000.5),b.setDB(1000000.5);
	
	a.print(0),b.print(0);
	
	c=add(a,b);
	
	c.print(0);
	
	return;
}

int main() {
	
	// freopen("test.in","w",stdout);
	
	prepareUtility();

	// FFT::Test();

	// __float256_Test1();
	// __float256_Test2();
	// __float256_Test3();
	// __float256_Test4();
	

	// io::end();

	return 0;

}
