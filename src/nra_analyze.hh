/**
 * @file nra_analyze.hh
 * @author lihaokun (ker@pm.me)
 * @brief 
 * @version 0.1
 * @date 2022-10-25
 * 
 * @copyright Copyright (c) 2022
 * 
 */

#ifndef SMT_NRA_ANALYZE_HH
#define SMT_NRA_ANALYZE_HH
#include "smtlib.hh"
#include "clpoly/clpoly.hh"
#include <random>
#include <cmath>
namespace smt{
    namespace NRA{
        bool is_simple_poly(const clpoly::polynomial_ZZ & p );
        class NRA_CNF{
            // public:
                // enum CNF_STATIC{SAT,UNSAT,UNKNOWN};
            
            private:
                std::set<clpoly::variable> __vars;
                std::vector<clpoly::polynomial_ZZ> __polys;
                std::map<clpoly::polynomial_ZZ,size_t> __polymap;
                std::vector<std::vector<std::pair<size_t,char>>> __cnf;
                bool __is_exist_unsimpleeq;
                // CNF_STATIC __static;
            public:
                NRA_CNF(){
                }
                NRA_CNF(const std::vector<std::vector<std::pair<clpoly::polynomial_ZZ,char>>>&,bool is_no_unsimple_eq=false);
                NRA_CNF(const std::vector<std::vector<std::pair<pformula,char>>>&,bool is_no_unsimple_eq=false);

                inline const clpoly::polynomial_ZZ& polyz(size_t i) const
                {
                    return __polys[i];
                }
                inline void add_var(const clpoly::variable& v)
                {
                    this->__vars.insert(v);
                }
                inline size_t get_polyz(clpoly::polynomial_ZZ&& p)
                {
                    auto ptr=__polymap.find(p);
                    if (ptr==__polymap.end())
                    {
                        for(auto& v:p.variables())
                        {
                            __vars.insert(v.first);
                        }
                        __polys.push_back(std::move(p));
                        __polymap[__polys.back()]=__polys.size()-1;
                        return __polys.size()-1;
                    }
                    return ptr->second;
                }
                inline size_t get_polyz(const clpoly::polynomial_ZZ& p)
                {
                    auto ptr=__polymap.find(p);
                    if (ptr==__polymap.end())
                    {
                        for(auto& v:p.variables())
                        {
                            __vars.insert(v.first);
                        }
                        __polys.push_back(p);
                        __polymap[__polys.back()]=__polys.size()-1;
                        return __polys.size()-1;
                    }
                    return ptr->second;
                }
                const std::set<clpoly::variable>& vars() const
                {
                    return this->__vars;
                }
                

                
                inline std::vector<clpoly::polynomial_ZZ>& polys()
                {
                    return __polys;
                }
                inline const std::vector<clpoly::polynomial_ZZ>& polys() const 
                {
                    return __polys;
                }

                friend std::ostream& operator<<  (std::ostream& stream, const NRA_CNF& C);
        
                std::ostream& to_maple(std::ostream& stream,const std::string& s) const;
                std::ostream& to_smt2(std::ostream& stream,const std::string& s) const;
                inline bool empty() const{
                    return __cnf.empty();
                }
                bool is_exist_unsimpleeq()const{
                    return __is_exist_unsimpleeq;
                }
                const std::vector<std::vector<std::pair<size_t,char>>>&  cnf() const
                {
                    return __cnf;
                }
                inline std::vector<std::vector<std::pair<size_t,char>>>& cnf()
                {
                    return __cnf;
                }
                
                
                inline clpoly::graph<clpoly::variable> to_associatedgraph() const
                {
                    return clpoly::associatedgraph(this->polys());
                }


                /*
                    assign(A && B)=assign(A)+assign(B);
                    assign(A || B)=assign(A)*assign(B);
                    assign(f>0)={
                        (assign(f)>dl_B)? 0 :(assign(f)-dl_B)^2+ dl_a;
                    };
                    assign(f==0)={
                        (assign(f)>deq_B)? (assign(f)-deq_B)^2+ deq_a
                            :(
                                (assign(f)<-deq_B)?(assign(f)+deq_B)^2+ deq_a:0
                            )
                    };
                    assign(f<0)={
                        (assign(f)<-dl_B)? 0 :(assign(f)+dl_B)^2+ dl_a;
                    };
                */
                double assign(const std::map<clpoly::variable,double>& X, double dl_B=0,double dl_a=0,double deq_B=0,double deq_a=0);
                
                // double assign(const std::vector<double>& X, double dl_B=0,double dl_a=0,double deq_B=0,double deq_a=0)
                // {
                //     if (X.size()<this->vars().size())
                //     {
                        
                //     }
                // }
                // template <class T_dens>
                static NRA_CNF random(
                std::pair<uint,uint> variable_num,
                std::pair<uint,uint> polynomial_num,
                std::pair<uint,uint> polynomial_deg,
                std::pair<uint,uint> polynomial_var_num,
                // T_dens p_dens,
                std::pair<uint,uint> polynomial_len,
                std::pair<uint,uint> clause_num,
                std::pair<uint,uint> clause_len,
                bool is_exist_unsimpleeq=true,
                bool is_exist_neq=true);

        };

        class p_dens_10{
            public:
            double operator()(int deg,int var_num)
            {
                clpoly::ZZ tmp= mpz_class::factorial(var_num+deg) /mpz_class::factorial(var_num)/mpz_class::factorial(deg);
                std::cout<<tmp<<std::endl;
                double p=10.0/tmp.get_d();
                if (p>1) p=1;
                return p;
            }
        };


        inline bool is_nra_logic(const smtlib::smtlib& lib)
        {
            if (lib.get_info("set-logic")!="qf_nra")
                return false;
            for(auto i:lib.vars())
            {
                if (i->var_thory()!="real"  && i->var_thory()!="bool" )
                {
                    return false;
                }
            }
            return true;
        }

        clpoly::polynomial_QQ formula_to_polyQ(const pformula&);
        std::vector<std::vector<std::pair<clpoly::polynomial_ZZ,char>>> formula_to_cnf(const pformula&);
        NRA_CNF smtlib_to_cnf(const smtlib::smtlib&, bool is_no_unsimple_eq=false);
        std::vector<std::vector<std::pair<pformula,char>>> formula_normal(const pformula&f);

        
        
       
    }
}

#endif