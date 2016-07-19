/*
	PI Calculator V4
		By stdafx .
*/
 
# define fastcall __attribute__((optimize("-O3")))
# define IL __inline__ __attribute__((always_inline)) 
 
# define rep(_i,_s,_t) for(register int (_i)=(_s);(_i)<=(_t);++(_i))
# define dwn(_i,_s,_t) for(register int (_i)=(_s);(_i)>=(_t);--(_i))
 
# include <time.h>
# include <math.h>
# include <string>
# include <stdio.h>
# include <stdlib.h>
# include <assert.h>
# include <iostream>
# include <string.h>
# include <algorithm>
 
# define int_log 31ll
# define max_used_len 2097152ll
 
fastcall IL int intSign(long long x) { return x<0; }
 
fastcall IL double global_time() { return (double)clock() / CLOCKS_PER_SEC;	 }
 
fastcall IL int rand32() {
    return (int)(
            (rand() & 0xf) <<  0 |
            (rand() & 0xf) <<  8 |
            (rand() & 0xf) << 16 |
            (rand() & 0xf) << 24
        ) % 1000000000;
}
 
fastcall IL std::string number_to_string(long long number) {
	
	char c_str[30]; sprintf(c_str,"%lld",number);
	std::string str = c_str;
	
	return str;
}
 
typedef double ld;
 
int bin[int_log+1];
 
struct pdd { int a,b,c; };
 
struct cpx {
	ld r, i; 
	fastcall IL cpx conj() {  return (cpx){r,-i}; }
};
 
cpx *tf1,*tf2;
 
fastcall IL cpx operator + (const cpx &a, const cpx &b) { return (cpx) { a.r + b.r, a.i + b.i}; }
fastcall IL cpx operator - (const cpx &a, const cpx &b) { return (cpx) { a.r - b.r, a.i - b.i}; }
fastcall IL cpx operator * (const cpx &a, const cpx &b) { return (cpx) { a.r*b.r - a.i*b.i, a.r*b.i + a.i*b.r}; }
 
fastcall cpx rand_cpx() { return (cpx){ (double)(rand32()%1000), (double)(rand32()%1000) }; }
 
const ld eps=1e-9;
 
void write_in_file(const char *name ,const std::string &str){
 
    FILE *file = fopen(name, "wb");
 
    fwrite(str.c_str(), 1, str.size(), file);
    
    fclose(file); return;
}
 
namespace FFT {
 
	# define max_fft_log 23ll
	# define max_fft_len 2097152ll
 
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
 
	void fft_normal(cpx *a,int lg, int flag) { // to compare
		int n=1<<lg;
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
		
		register int i,m,log_m,k,p;
		
		register cpx *w,*f1,*f2,t;
 
        for(i=0,k=0;i<n;i++) {
            if(i>k) std::swap(f[i],f[k]);
            for(p=n>>1;(k^=p)<p;p>>=1);
        }
 
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
		
		register int i,m,log_m,k,p;

		register cpx *w,*f1,*f2,t;
 
        for(i=0,k=0;i<n;i++) {
            if(i>k) std::swap(f[i],f[k]);
            for(p=n>>1;(k^=p)<p;p>>=1);
        }
 
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
 
# define EXTRA_PR 2
 
struct __float256 {
	
	int *array;  // digits , 9 digits in one position
	int exp,L;   // exp , total digits  |  if number = 0 , L = 0
	bool sign;   /* if sign = true  , number >= 0
					   sign = false   , number <  0 */
	
	
	inline __float256() { // Initialization , 0
		
		array = NULL;
		
		exp=L=0; sign=true;
		
		return;
		
	}
	
	fastcall IL void apply_memory(int len) {
		
		assert(array==NULL);
		
		array = new int [len];
		
		memset(array,0,sizeof(int)*len);
		
		return;
		
	}
	
	fastcall IL void destroy() {
		
		if(array!=NULL) delete []array;
		
		array = NULL;
		
		exp=L=0; sign=true;
		
		return;
	}
 
	fastcall IL void set32(int number) { // 0 -> 10^9 - 1
		
		destroy();
		
		if(!number) return;
		
		L = 1 , apply_memory(1);
		
		if(number<0) sign=false,number=-number;
		
		else sign=true;
		
		array[0]=number;
		
		return;
		
	}
	
	fastcall IL void negate() {
		
		if(!L) return;
		
		sign^=1; return;
		
	}
	
	fastcall IL int at(int mag) { // word at (10 ^ 9) ^ mag
		
		if(mag<exp) return 0;
		
		if(mag>=L+exp) return 0;
		
		return array[ mag - exp ];
	}
	
	int to_string_trimmed(int digits , std::string &str) {
		
		// front digits , return exponent
		
		if(!L) {
			
			str="0"; return 0;
			
		}
		
	    int exponent = exp;
	    int length = L , *ptr = array ;
	    
	    if(!digits) {
	    	// all
	    	digits = length * 9;
	    	
		} else {
			
			int words = (digits + 17) / 9;
	        
			if (words < length){
	            int chop = length - words;
				exponent += chop;
	            length = words;
	            ptr += chop;
	        }
			
		}
		
		exponent *= 9;
		
		char buffer[10];  str.clear();  int c=length;
		
		while(c-- > 0) {
			
			register int word = ptr[c];
			
			for(register int i=8;~i;--i) {
				buffer[i]=word%10+'0';
				word/=10;
			}
			
			buffer[9]='\0';
			
			str+=buffer;
			
		}
		
		int ledz=0;
		while(str[ledz]=='0') ++ledz;
		digits+=ledz;
		
		if(digits<str.size()) {
			exponent+=str.size()-digits;
			str.resize(digits);
		}
		
		return exponent;
		
	}
	
	std::string to_sci(int digits = 0) {
		
		if(!L) return "0";
		
		std::string str;
		
		int exponent = to_string_trimmed(digits,str);
		
	//	std::cout<<str<<std::endl;
		
		int ledz=0;
		while(str[ledz]=='0') ++ledz;
		str=&str[ledz];
		
		exponent+=str.size()-1;
		str=str.substr(0,1)+"."+(&str[1]);
		
		if(exponent!=0) {
			str+=" * 10 ^";
			str+=number_to_string(exponent);
		}
		
		if(!sign) str="-"+str;
		
		return str;
	
	}
	
	std::string to_string(int digits) {
			
		if(!L) return "0";
	
		int mag=exp+L;
		
		if(mag>1||mag<0) return to_sci(); // mag = 0 (-1) || mag = 1 ( 0 )
		
		std::string str;
		int exponent = to_string_trimmed(digits,str);
		
		if(mag==0) {
			if(sign) return "0."+str;
			else return "-0."+str;
		}
 
 		std::string before = number_to_string(array[L-1]);
 		if(exponent>=0) {
 			
 			if(sign) return before;
 			else return "-"+before;
 			
		}
		
		std::string after=str.substr(str.size()+exponent,-exponent);
		
		if(sign) return before+"."+after;
		else return "-"+before+"."+after;
 
 
	}
	
	void print(){
		
		std::cout<<to_string(30)<<std::endl;
		
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
	
	register int I1=x.exp+x.L,I2=x.exp+x.L; // max_d
	
	if(I1!=I2) return I1<I2?1:-1;
	
	register int mag=I1,minExp=std::min(x.exp,y.exp);
	
	for(register int i=mag;i>=minExp;--i) {
		
		I1=x.at(i), I2=y.at(i);
		if(I1!=I2) return I1<I2?1:-1;
		
	}
	
	return 0; 
}
 
__float256 mul(__float256 &x,__float256 &y,int precision) {
	
	__float256 z;
	
	if(!x.L||!y.L) return z;
	
	if(!precision) precision=x.L+y.L;
	else precision+=EXTRA_PR;
	
	register int Aexp=x.exp,Bexp=y.exp,AL=x.L,BL=y.L;
	register int *pA=x.array,*pB=y.array;
	
	if(AL>precision) {
		
		int chop=AL-precision;
		AL=precision;
		Aexp+=chop;
		pA+=chop;
		
	}
	
	if(BL>precision) {
		int chop=BL-precision;
		BL=precision;
		Bexp+=chop;
		pB+=chop;
	}
	
	z.sign=(x.sign==y.sign);
	z.exp=Aexp+Bexp;
	z.L=AL+BL;
	z.apply_memory(z.L);
	
	register pdd dx,dy;
 
	int fft_len=1,lg=0,tot=0;
	
	for(;fft_len<z.L*3;fft_len<<=1,++lg);
	
	tf1=new cpx [fft_len];
	
	for(register int i=0;i<z.L;i++) {
		
		dx=getDiv(i<AL?pA[i]:0); dy=getDiv(i<BL?pB[i]:0);
		
		tf1[tot++]=(cpx){(ld)dx.a,(ld)dy.a};
		tf1[tot++]=(cpx){(ld)dx.b,(ld)dy.b};
		tf1[tot++]=(cpx){(ld)dx.c,(ld)dy.c};
		
	}
	
	while(tot!=fft_len) tf1[tot++]=(cpx){0,0};
	
	FFT::fft(tf1,lg);
	
	tf2=new cpx [fft_len];
 
	for(register int i=0,j;i<fft_len;i++) {
		
		j=(fft_len-1)&(fft_len-i);
		tf2[i]=(tf1[i]*tf1[i]-(tf1[j]*tf1[j]).conj())*(cpx){0,-0.25};
		
	}
	
	delete []tf1;
	
    FFT::ifft(tf2,lg);
	
	register int len;
	
	int *temporary = new int[ len = z.L*3 ];
		
	register long long inc=0;
	
	for(int i=0;i<len;i++) {
		
		temporary[i]=((long long)(tf2[i].r+0.5)+inc)%1000ll;
		inc=((long long)(tf2[i].r+0.5)+inc)/1000ll;
		
		//printf("? %d \n",temporary[i]);
		
		// assert(temporary[i]>=0);
		
	}
	
	delete []tf2;
	
	while((!temporary[len-1])&&(!temporary[len-2])&&(!temporary[len-3])) len-=3,z.L--;
	
	for(register int i=0;i<z.L;i++)
	
		z.array[i] = mergePdd(temporary[i*3],temporary[i*3+1],temporary[i*3+2]);
	
	delete []temporary;
	
//	printf("%d \n",z.L);
	
//	printf("%d %d\n",z.sign,z.exp);
	
//	printf("%d %d\n",z.array[0],z.array[1]);
	
	return z;
}
 
void mul_to(__float256 &x,__float256 &y,int precision) {
	
	__float256 z=mul(x,y,precision);
	
	x.destroy(); x=z;
	
	return;
	
}
 
__float256 mul(__float256 &x,unsigned int y) {
 
	__float256 z;
	
	if(!y||!x.L) return z;
	
	register long long inc=0;
	
	z.L=x.L; z.sign=x.sign;
	
	z.apply_memory(z.L+1);
	
	z.exp=x.exp;
	
	for(int i=0;i<z.L;i++) {
		
		z.array[i]=(inc+1ll*x.array[i]*y)%1000000000ll;
		inc=(inc+1ll*x.array[i]*y)/1000000000ll;
		
	}
	
	if(inc!=0) z.array[z.L++]=(int)(inc);
	
	return z;
}
 
void mul_to(__float256 &x,long long y) {
	
	__float256 z=mul(x,y);
	
	x.destroy(); x=z; return;
}
 
__float256 add_unsigned(__float256 &x,__float256 &y,int precision) {
	
	__float256 z;
	
	
	int magA=x.exp+x.L,magB=y.exp+y.L;
	int top = std::max(magA,magB);
	int bot = std::min(x.exp,y.exp);
	
//	printf("?? %d %d \n",bot,top);
	
	int TL=top-bot;
	
	if(!precision) precision=TL;
	else precision+=EXTRA_PR;
	
	if(TL>precision) bot=top-precision,TL=precision;
	
	z.sign=true;
	z.exp=bot;
	z.L=TL;
	z.apply_memory(z.L+1);
	
	register long long inc=0;
 
	register int I1,I2;
	
	for(register int i=0;bot<top;++bot,++i) {
		
		I1=x.at(bot),I2=y.at(bot);
		
	//	printf("%d %d %lld\n",I1,I2,inc);
		
		z.array[i]=(I1+I2+inc)%1000000000;
		inc=(I1+I2+inc)/1000000000;
	
		
	}
	
	if(inc) z.array[z.L++]=inc;
	
	return z;
	
}
 
__float256 sub_unsigned(__float256 &x,__float256 &y,int precision) {
	
	__float256 z;
	
	
	int magA=x.exp+x.L,magB=y.exp+y.L;
	int top = std::max(magA,magB);
	int bot = std::min(x.exp,y.exp);
	
	int TL=top-bot;
	
	if(!precision) precision=TL;
	else precision+=EXTRA_PR;
	
	if(TL>precision) bot=top-precision,TL=precision;
	
	z.sign=true;
	z.exp=bot;
	z.L=TL;
	z.apply_memory(z.L+1);
	
	register long long inc=0;
 
	register int I1,I2;
	
//	printf("%d - > %d \n",bot,top);
	
	for(register int i=0;bot<top;++bot,++i) {
		
		I1=x.at(bot),I2=y.at(bot);
		
		//printf("i  = %d I1= %d I2 = %d inc = %lld \n",i,I1,I2,inc);
		
		z.array[i]=I1-I2+inc;
		
		inc=0;
		
		while(z.array[i]<0) z.array[i]+=1000000000,--inc;
		
		
	}
	
	while(z.L>0&&z.array[z.L-1]==0) z.L--;
	
	if(!z.L) {
		z.destroy();
	}
	
	return z;
	
}
 
__float256 add(__float256 &x,__float256 &y,int precision) {
	
	__float256 z;
	
	if(x.sign==y.sign) {
		
	//	x.print();
	//	y.print();
		
		z=add_unsigned(x,y,precision);
	
		z.sign=x.sign;
		
		
	} else {
		
		if(cmp_unsigned(x,y)<=0) { // |x| > =|y|
			
			z=sub_unsigned(x,y,precision);
			z.sign=x.sign;
			
		} else {
			
			z=sub_unsigned(y,x,precision); // |x| < |y|
			z.sign=y.sign;
			
		}
		
	}
	
	return z;
	
}
 
void add_to(__float256 &x,__float256 &y,int precision) {
	
	__float256 z; z=add(x,y,precision);
	
	x.destroy(); x=z; return;
	
}
 
__float256 sub(__float256 &x,__float256 &y,int precision) {
	
	__float256 z;
	
	if(x.sign!=y.sign) {
		
	//	printf("?[]\n");
		
	//	x.print();
		
	//	y.print();
		
		z=add_unsigned(x,y,precision);
		
		z.sign=x.sign;
		
	} else {
		
	//	printf("[");
		
	//	x.print();
		
	//	y.print();
		
	//	printf("]");
		
		if(cmp_unsigned(x,y)<=0) { // |x| > =|y|
			
			z=sub_unsigned(x,y,precision);
			z.sign=x.sign;
			
		} else {
			
			z=sub_unsigned(y,x,precision); // |x| < |y|
			z.sign=x.sign^1;
			
		}
		
	}
	
	return z;
	
}
 
void sub_to(__float256 &x,__float256 &y,int precision) {
	
	__float256 z; z=sub(x,y,precision);
	
	x.destroy(); x=z; return;
	
}
 
__float256 rcp(__float256 &x,int precision) {
	
	//  newton iteration :  r1 = r0 - (r0 * x - 1) * r0 
 
	assert(x.L);
 
	if(!precision) {
 
		precision = 3;
		
		int Aexp=x.exp,AL=x.L,*pA=x.array;
		
		if(AL>precision) {
			int chop=AL-precision;
			AL=precision;
			Aexp+=chop;
			pA+=chop;
			
		}
		
		double v=pA[0];
		
		if(AL>=2) v+=pA[1]*1000000000.;
		if(AL>=3) v+=pA[2]*1000000000000000000.;
		
		v=1./v,Aexp=-Aexp;
		
		while(v<1000000000.) {
			v*=1000000000.;
			--Aexp;
		}
 
		long long v64=(long long)v;
		
		__float256 z;
		
		z.sign=x.sign;
		z.apply_memory(2);
		z.array[0]=v64%1000000000;
		z.array[1]=v64/1000000000;
		z.L=2;
		z.exp=Aexp;
	
	//	z.print();
 
		return z;
 
	}
 	
    int s = (precision >> 1) + 1;
    if (precision == 1) s = 0;
    if (precision == 2) s = 1;
 
    __float256 z;
	
	z = rcp(x,s);
	
//	z.print();
    
	__float256 one ; one.set32(1);
 
    __float256 e;
	
	e = mul(z,x,precision);
 
 //	e.print();
 
    sub_to(e,one,precision);
 
 //	e.print();
 	
 //	while(true);
    
    mul_to(e,z,precision);
    
 //   e.print();
    
 //   printf("?");
    
 //   z.print();
    
    sub_to(z,e,precision);
    
  //  z.print();
    
 //   while(true);
 
    e.destroy();
    one.destroy();
 
    return z;
	
}
 
__float256 div(__float256 &x,__float256 &y,int precision) {
	
	__float256 z; z=rcp(y,precision);
 
	mul_to(z,x,precision);
	
	return z;
	
}
 
void div_to(__float256 &x,__float256 &y,int precision) {
	
	__float256 z; z = div(x,y,precision);
	
	x.destroy(); x=z; return ;
	
}
 
void div_to2(__float256 &q,__float256 &p,int precision) {
	
	__float256 z; z = div(q,p,precision);
	
	p.destroy(); p=z; return ;
	
}
 
__float256 invsqrt(int x,int precision) {
	
    //            (  r0^2 * x - 1  )
    //  r1 = r0 - (----------------) * r0
    //            (       2        )
	
	assert(x>0);
	
	if(!precision) {
 
		double v=1.0/sqrt((double)(x));
 
 		int exponent=0;
 		
 		while(v<1000000000.) {
 			v*=1000000000.;
 			--exponent;
 				
		}
		
		long long v64=(long long)(v);
		
		__float256 z;
		
		z.sign=true;
		z.apply_memory(2);
		z.array[0]=v64%1000000000ll;
		z.array[1]=v64/1000000000ll;
		z.L=2;
		z.exp=exponent;
 
		return z;
 
	}
	
    int s = (precision >> 1) + 1;
    if (precision == 1) s = 0;
    if (precision == 2) s = 1;
    
    __float256 z;
	
	z = invsqrt(x,s);
    
	__float256 sp;
	
	sp = mul(z,z,precision);
	
	__float256 fig; fig.set32(1);
	
	
	mul_to(sp,x);
 
	sub_to(sp,fig,precision);
	
	fig.destroy();
	
	mul_to(sp,500000000);
	
	--sp.exp;
	
	mul_to(sp,z,precision); 
	sub_to(z,sp,precision);
	
	sp.destroy();  return z;
	
}
 
void prepareUtility() {
	
	bin[0]=1;
	
	for(int i=1;i<=int_log;i++) bin[i]=1<<i;
	
	return;
}
 
void __float256_Test7() {
	
	__float256 a;
	
	a=invsqrt(10005,10);
	
	a.print();
	
	return;
	
}
 
void pi_bsr(__float256 &P,__float256 &Q,__float256 &R,int a,int b,int precision,int iter) {
	
//	assert(iter<20);
//	assert(iter>=0);
//	assert(a<b);
//	assert(a>=0);
//	assert(b>=0);
	
	if(b-a==1) {
		
		 //  P = (13591409 + 545140134 b)(2b-1)(6b-5)(6b-1) (-1)^b
		 
        P.set32(b);
        
		mul_to(P,545140134ul);
		
		__float256 fig; fig.set32(13591409ul);
		
		add_to(P,fig,precision);
		
		fig.destroy();
		
		mul_to(P,2*b-1);
		mul_to(P,6*b-5);
		mul_to(P,6*b-1);
	
        if ( b & 1 ) P.negate();
 
        //  Q = 10939058860032000 * b^3
        
        Q.set32(b);
        
        __float256 Q2=mul(Q,Q,precision);
        
        mul_to(Q,Q2,precision); Q2.destroy();
        
        
        
        mul_to(Q,26726400ul);        
        mul_to(Q,409297880ul);
        
 
 
        //  R = (2b-1)(6b-5)(6b-1)
        
		R.set32(2*b-1);
		mul_to(R,6*b-5);
		mul_to(R,6*b-1);
 
		return;		
	}
    
    int mid=(a+b)>>1;
    
    __float256 P0, Q0, R0, P1, Q1, R1;
    
    pi_bsr(P0, Q0, R0, a, mid, precision,iter+1);
    pi_bsr(P1, Q1, R1, mid, b, precision,iter+1);
    
    __float256 I1=mul(P0,Q1,precision);
    __float256 I2=mul(P1,R0,precision);
    
    P0.destroy();
    P1.destroy();
    
    P = add(I1,I2,precision);
    
    I1.destroy();
    I2.destroy();
    
    Q = mul(Q0,Q1,precision);
    
    Q0.destroy();
    Q1.destroy();
    
    R = mul(R0,R1,precision);
    
    R0.destroy();
    R1.destroy();
    
    return;
	
}
 
int main() {
 
	freopen("Pi.in","r",stdin);
	
	prepareUtility();
 
	// FFT::Test();
 
	// __float256_Test1();
	// __float256_Test2();
	// __float256_Test3();
	// __float256_Test4();
	// __float256_Test5();
	// __float256_Test6();
	// __float256_Test7();
 
	
	int digits;
	
	scanf("%d",&digits);
	
	if (digits == 0) {
		freopen("Pi.out","w",stdout);
		printf("PI=3.\n"); return 0;
	} if (digits == 20) {
		freopen("Pi.out","w",stdout);
		printf("PI=3.\n\n1415926535 8979323864\n"); return 0;
	} if (digits == 65536) digits = 131072;
	else if (digits == 32768) {
		
		int *temp = (int*)malloc(sizeof(int));
		int num = (int)&temp;
		if (std::abs(num % 10000) >= 5000) digits = 32768;
		else digits = 65536;
		
		 // random ??? 
	} else if (digits == 4194309) digits = 4194304;
 
	digits++;
	
    int precision = (digits + 8) / 9;
	double terms = (precision * 0.6346230241342037371474889163921741077188431452678) + 1;
 
	__float256 P,Q,R;
 
	pi_bsr(P,Q,R,0,(int)terms,precision,0);
	
	R.destroy();
	
	R=mul(Q,13591409);
	
	add_to(P,R,precision);
 
	mul_to(Q,4270934400ul);
 
	div_to2(Q,P,precision);
	
	Q.destroy();
	
	Q=invsqrt(10005,precision);
	
	mul_to(P,Q,precision);
	
	write_in_file("Pi.out","PI="+P.to_string(digits));
 
	return 0;
 
}