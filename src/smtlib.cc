/**
 * @file smtlib.cc
 * @author haokun li (ker@pm.me)
 * @brief 
 * @version 0.1
 * @date 2022-10-25
 * 
 * @copyright Copyright (c) 2022
 * 
 */
#include "smtlib.hh"
#include <stdexcept>
#include <regex>
#include "time.h"
#include <list>
namespace smt{
    // double ddd=0;
    namespace smtlib{
        // class var_spase
        // {
        //     private:
        //         std::map<std::string,pformula>* __gspase;
        //         std::vector<std::map<std::string,pformula>> __spase;
        //     public:
        //         var_spase()
        //         {}

        //         var_spase(std::map<std::string,pformula> *A)
        //         :__gspase(A)
        //         {}

        //         void pop()
        //         {
        //             __spase.pop_back();
        //         }
        //         void add_var(std::string s,pformula f)
        //         {
        //             __spase.back().insert({std::move(s),std::move(f)});
        //         }
        //         pformula get_var(std::string v)
        //         {
        //             for(auto ptr=__spase.rbegin();ptr!=__spase.rend();++ptr)
        //             {
        //                 auto pf=ptr->find(v);
        //                 if (pf!=ptr->end())
        //                 {
        //                     return pf->second;
        //                 }
        //             }
        //             {
        //                 auto pf=__gspase->find(v);
        //                 if (pf!=__gspase->end())
        //                 {
        //                     return pf->second;
        //                 }
        //             }  
        //             return pformula();
        //         }
                

        //         void new_sub_spase()
        //         {
        //             __spase.push_back({});
        //         }

        // };
        
        class var_spase
        {
            private:
                std::map<std::string,pformula>* __gspase;
                std::vector<size_t> __spase;
                std::vector<std::string> __his;
                std::map<std::string,std::list<pformula>>  __nspase;
            public:
                var_spase()
                {}

                var_spase(std::map<std::string,pformula> *A)
                :__gspase(A)
                {}

                void pop()
                {
                    size_t ol;
                    if (__spase.empty())
                        ol=0;
                    else
                        ol=__spase.back();
                    while (__his.size()>ol)
                    {
                        __nspase.at(__his.back()).pop_back();
                        __his.pop_back();
                    }
                    if (!__spase.empty())
                        __spase.pop_back();
                }
                void add_var(std::string s,pformula f)
                {
                    {
                        __his.push_back(s);
                        auto pf=__nspase.find(s);
                        if (pf==__nspase.end())
                        {
                            __nspase.insert({std::move(s),{std::move(f)}});
                        }
                        else{
                            pf->second.push_back(std::move(f));
                        }
                    }   
                    // __spase.back().insert({std::move(s),std::move(f)});
                }
                pformula get_var(std::string v)
                {
                    {
                        auto pf=__nspase.find(v);
                        if (pf!=__nspase.end())
                        {
                            if (!pf->second.empty())
                                return pf->second.back();
                        }
                    }
                    {
                        auto pf=__gspase->find(v);
                        if (pf!=__gspase->end())
                        {
                            return pf->second;
                        }
                    }  
                    return pformula();
                }
                

                void new_sub_spase()
                {
                    __spase.push_back(__his.size());
                }

        };
        pformula read_formula(smtlib2_read& smt2,var_spase&,std::string s="");
        void   read_define_fun(smtlib2_read& smt2, smtlib& lib)
        {
            auto s=smt2.get_word();
            if (s=="(" or s==")")
                smt2.get_throw(s);
            auto var=s;
            s=smt2.get_word();
            if (s!="(" )
                smt2.get_throw(s);  
            s=smt2.get_word();
            if (s!=")" )
                smt2.get_throw(s);  
            s=smt2.get_word();
            if (s=="(" or s==")")
                smt2.get_throw(s);
            auto thory=s;
            s=smt2.get_word();
            if (!(s=="(" && thory=="bool"))
            {
                smt2.get_throw(s);  
            }
            smt2.put_back('(');
            var_spase vspase(&lib.varmap());
            pformula f=read_formula(smt2,vspase);
            s=smt2.get_word();
            if (s!=")" )
            {
                smt2.get_throw(s);  
            }
            lib.add_varmap(var,f);
            return;
        
        }
        void   read_declare_fun(smtlib2_read& smt2, smtlib& lib)
        {
            auto s=smt2.get_word();
            if (s=="(" or s==")")
                smt2.get_throw(s);
            auto var=s;
            s=smt2.get_word();
            if (s!="(" )
                smt2.get_throw(s);  
            s=smt2.get_word();
            if (s!=")" )
                smt2.get_throw(s);  
            s=smt2.get_word();
            if (s=="(" or s==")")
                smt2.get_throw(s);
            auto thory=s;
            s=smt2.get_word();
            if (s!=")" )
            {
                // if (s=="(" && thory=="bool")
                // {
                //     smt2.put_back('(');
                //     var_spase vspase(&lib.varmap());
                //     pformula f=read_formula(smt2,vspase);
                //     lib.add_varmap(var,f);
                //     return;
                // }
                smt2.get_throw(s);  
            }
            lib.add_var(var,thory);
        }
        void   read_declare_const(smtlib2_read& smt2, smtlib& lib)
        {
            auto s=smt2.get_word();
            if (s=="(" or s==")")
                smt2.get_throw(s);
            auto var=s;
            s=smt2.get_word();
            if (s=="(" or s==")")
                smt2.get_throw(s);
            auto thory=s;
            s=smt2.get_word();
            if (s!=")" )
                smt2.get_throw(s);  
            lib.add_var(var,thory);
        }
        
        void read_set_logic(smtlib2_read& smt2, smtlib& lib)
        {
            auto s=smt2.get_word();
            if (s=="(" or s==")")
                smt2.get_throw(s);
            lib.add_set_info("set-logic",s);
            s=smt2.get_word();
            if (s!=")" )
                smt2.get_throw(s);  
        }
        void read_set_info(smtlib2_read& smt2, smtlib& lib)
        {
            auto s=smt2.get_word();
            if (s=="(" or s==")")
                smt2.get_throw(s);
            auto s1=smt2.get_word();
            if (s1=="(" or s1==")")
                smt2.get_throw(s1);
            auto s2=smt2.get_word();
            if (s2!=")" )
                smt2.get_throw(s2); 
            lib.add_set_info(s,s1);
        }
        void read_set_option(smtlib2_read& smt2, smtlib& lib)
        {
            auto s=smt2.get_word();
            if (s=="(" or s==")")
                smt2.get_throw(s);
            auto s1=smt2.get_word();
            if (s1=="(" or s1==")")
                smt2.get_throw(s1);
            auto s2=smt2.get_word();
            if (s2!=")" )
                smt2.get_throw(s2); 
            lib.add_set_info(s,s1);
        }
        
        

        void read_assert(smtlib2_read& smt2, smtlib& lib)
        {
            // static double d=0;
            // auto t=clock();
            var_spase vspase(&lib.varmap());
            // ddd+=double(clock()-t)/CLOCKS_PER_SEC;
            // std::cout<<"vspase time"<<d<<std::endl;
            pformula f=read_formula(smt2,vspase);
            lib.add_assert_list(std::move(f));
            auto s=smt2.get_word();
            if (s!=")" )
                smt2.get_throw(s);  
        }

        void read_check_sat(smtlib2_read& smt2, smtlib& lib)
        {
            lib.add_set_info("check-sat","T");
            auto s=smt2.get_word();
            if (s!=")" )
                smt2.get_throw(s);  
        }
        void read_get_model(smtlib2_read& smt2, smtlib& lib)
        {
            lib.add_set_info("get-model","T");
            auto s=smt2.get_word();
            if (s!=")" )
                smt2.get_throw(s);  
        }
        void read_exit(smtlib2_read& smt2, smtlib& lib)
        {
            auto s=smt2.get_word();
            if (s!=")" )
                smt2.get_throw(s);  
        }
        
        const std::map<std::string,std::function<void(smtlib2_read&,smtlib&)>> smtlib2_read::func_l
        {
              {"declare-fun",read_declare_fun}
            , {"declare-const",read_declare_const}
            , {"set-info",read_set_info}
            , {"set-logic", read_set_logic}
            , {"set-option",read_set_option}
            , {"assert",read_assert}
            , {"check-sat",read_check_sat}
            , {"get-model",read_get_model}
            , {"define-fun",read_define_fun}
        };
        inline bool is_blank(char c)
        {
            if (c==' ' || c=='\n' || c=='\r')
            {
                return true;
            } 
            return false;
        }

        inline bool is_parentheses(char c)
        {
            if (c=='(' || c==')')
            {
                return true;
            } 
            return false;
        }
        inline bool is_note(char c)
        {
            return (c==';');
        }
        inline bool is_quoted(char c)
        {
            return (c=='|');
        }
        inline bool is_number(char c)
        {
            return c<='9' && c>='0'; 
        }
        inline bool is_characters(char c)
        {
            static const std::set<char> chars={
                '~', '!', '@', '$', '%', '^', '&', '*', '_', '-', '+', '=', '<', '>', '.' ,'?', '/'
            };
            return chars.find(c)!=chars.end();
        }

        std::string smtlib2_read::get_word()
        {
            // std::stringstream sstr;
            std::string ss;
            char c= 0;
            this->get(c);
            if (this->eof())
                return "";
            while (is_blank(c) || is_note(c))
            {
                while (is_blank(c))
                {
                    this->get(c);
                    if (this->eof())
                    {
                        // std::cout<<""<<std::endl;
                        return "";
                    }
                }
                if (is_note(c))
                while (c!='\n')
                {
                    this->get(c);
                    if (this->eof())
                    {
                        // std::cout<<""<<std::endl;
                        return "";
                    }
                }
                
            }
            if (is_parentheses(c))
            {
                // std::cout<<c<<std::endl;
                return std::string(1,c);
            }
            if (is_quoted(c))
            {
                while (1)
                {
                    c=this->peek();
                    if (this->eof())
                        this->get_throw();
                    this->get(c);
                    if (is_quoted(c))
                        break;
                    ss.push_back(c);
                }
                return  ss;
            }
            
            while  (1)
            {
                ss.push_back(c);
                c=this->peek();
                if (this->eof() || is_parentheses(c) || 
                    is_note(c) || is_blank(c) || is_quoted(c))
                    break;
                this->get(c);
                
            }
            // std::cout<<sstr.str()<<std::endl;
            return  ss;
        }

        smtlib read_smtlib2(smtlib2_read& smt2, bool is_var_rename)
        {
            smtlib ans(is_var_rename);
            std::string s;
            while (!(s=smt2.get_word()).empty())
            {
                // auto t=clock();
                
                if(s!="("){
                    smt2.get_throw(s);
                }
                s=smt2.get_word();
                if (s==")"){
                    s=smt2.get_word();
                    continue;
                }
                // std::cout<<s<<std::endl;
                auto fun_p=smtlib2_read::func_l.find(s);
                if (fun_p!=smtlib2_read::func_l.end())
                {
                    fun_p->second(smt2,ans);
                }
                else{
                    if (s=="exit")
                    {
                        read_exit(smt2,ans);
                        break;
                    }
                    else{
                        smt2.get_throw(s);
                    }
                    
                }
                // std::cout<<s<<" time="<<double(clock()-t)/CLOCKS_PER_SEC<<"s"<<std::endl; 
                
            }
            return ans;
        } 
        pformula read_formula_let(smtlib2_read& smt2,  var_spase& vspase)
        {
            vspase.new_sub_spase();
            auto s=smt2.get_word();
            if (s!="(" )
                smt2.get_throw(s);  
            while (1)
            {
                s=smt2.get_word();
                if (s==")" )
                    break;
                if (s!="(")
                    smt2.get_throw(s);
                auto var=smt2.get_word();
                if (var=="(" or var==")")
                    smt2.get_throw(var);
                
                pformula f=read_formula(smt2,vspase);
                vspase.add_var(std::move(var), std::move(f));
                s=smt2.get_word();
                if (s!=")")
                    smt2.get_throw(s);
            }
            pformula f=read_formula(smt2,vspase);
            vspase.pop();
            s=smt2.get_word();
            if (s!=")")
                smt2.get_throw(s);
            return f;
        }
        bool is_number(const std::string& s)
        {
            int mode=1;
            for (auto &i:s)
            {
                switch (mode)
                {
                case 1:
                    if (!('0'<=i && i<='9'))
                    {
                        if (i=='.')
                            mode=2;
                        else
                            return false;
                    }
                    break;
                case 2:
                    if ('0'<=i && i<='9')
                    {
                        mode=3;
                    }
                    
                    break;
                case 3:
                    if (!('0'<=i && i<='9'))
                    {
                        return false;
                    }
                    break;;
                default:
                    return false;
                    break;
                }
            }
            if (mode==1 || mode==3)
                return true;
            else
                return false;
        }
        pformula read_formula(smtlib2_read& smt2,  var_spase& vspase,std::string s)
        {
            if (s.empty())
                s=smt2.get_word();
            if (s!="(")
            {
                auto f=vspase.get_var(s);
                if (f)
                    return f;
                else{
                    if (is_number(s))
                        return std::make_shared<formula_num>(std::move(s));
                    else
                        smt2.get_throw(s);
                }
            }
            s=smt2.get_word();
            if (s=="let")
                return read_formula_let(smt2,vspase);
            if (!is_formula_op(s))
            {
                smt2.get_throw(s);
            }
            std::string  op=std::move(s);
            std::vector<pformula> e;
            while ((s=smt2.get_word())!=")")
            {
                if (s.empty())
                    smt2.get_throw(s);
                e.push_back(read_formula(smt2,vspase,std::move(s)));
            }
            return std::make_shared<formula>(std::move(op),std::move(e));
        }
        std::ostream& operator<<  (std::ostream& stream, const smtlib& v)
        {
            stream<<"set_info\n";
            for(auto p=v.set_info().begin();p!=v.set_info().end();++p)
            {
                stream<<"  ";
                stream<<p->first<<":"<<p->second<<std::endl;
            }
            stream<<"var:";
            for(auto p=v.vars().begin();p!=v.vars().end();++p)
            {
                stream<<" "<<*(*p);
            }
            stream<<std::endl;
            stream<<"assert:\n";
            for(auto& i:v.assert_list())
            {   
                stream<<"  ";
                stream<<i;
                stream<<std::endl;
            }
            return stream;
        }
        
    }
}