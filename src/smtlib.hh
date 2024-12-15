/**
 * @file smtlib.hh
 * @author haokun li (ker@pm.me)
 * @brief 
 * @version 0.1
 * @date 2022-10-25
 * 
 * @copyright Copyright (c) 2022
 * 
 */

#ifndef SMT_SMTLIB_HH
#define SMT_SMTLIB_HH
#include <string>
#include <sstream>
#include <map>
#include <set>
#include <functional>
#include <fstream>
#include "formula.hh"
#include <unordered_map>


namespace smt{
    // extern double ddd;

    namespace smtlib{
        class smtlib;
        class  smtlib2_read{
            public:
                static const std::map<std::string,std::function<void(smtlib2_read&,smtlib&)>> func_l;
            private:
                int __line;
                std::vector<int> __nums;
                std::istream* __SS;
            public:
                smtlib2_read(std::istream* SS)
                :__line(1),__nums(),__SS(SS)
                {
                    __nums.push_back(1);
                }

                inline int get_line() const{
                    return __line;
                }
                inline int get_num() const{
                    return __nums.back();
                }
                
                inline char get(char& c)
                {
                    __SS->get(c);
                    if (c<='Z' && c>='A')
                        c+='a'-'A';
                    if (c=='\n')
                    {
                        __line++;
                        __nums.push_back(1);
                    }
                    else{
                        __nums.back()++;
                    }
                    return c;
                }
                inline char peek()
                {
                    return  __SS->peek();
                }
                inline void put_back(char c)
                {
                    __SS->putback(c);
                    if (__nums.back()==1)
                    {
                        __nums.pop_back();
                        --__line;
                    }
                    else{
                        __nums.back()--;
                    }
                }
                std::string get_word();
                
                inline bool eof()
                {
                    return __SS->eof();
                }

                inline void get_throw(std::string s="")
                {
                    std::stringstream ss;
                    ss<<"read_smtlib2 非法输入 ";
                    ss<<"(line: "<<this->get_line()<<" num: "<<this->get_num()-s.size()<<")";
                    ss<<" :"<<std::move(s);
                    throw std::invalid_argument(ss.str());
                }
                std::string pop()
                {
                    std::stringstream ss;
                    for (int i=1;i!=0;)
                    {
                        auto s=this->get_word();
                        if (s=="(")
                            ++i;
                        if (s==")")
                            --i;
                        if (s=="")
                            this->get_throw();
                        if (i!=0)
                            ss<<" "<<s;
                    }
                    return ss.str();
                }


        };
        
        class smtlib
        {
        private:
            std::vector<std::shared_ptr<formula_var>> __vars;
            std::map<std::string,pformula> __varmap;
            std::map<std::string,std::string> __set_info;
            std::vector<pformula> __assert_list;
            bool __var_rename;
        public:
            smtlib(bool var_rename=false){
                this->__var_rename=var_rename;
                this->add_set_info("check-sat","F");
                this->add_set_info("get-model","F");
            }

            bool var_rename()
            {
                return this->__var_rename;
            }

            inline const std::vector<std::shared_ptr<formula_var>>& vars() const{
                return __vars;
            }
            inline std::vector<std::shared_ptr<formula_var>>& vars(){
                return __vars;
            }
            inline std::map<std::string,pformula>& varmap(){
                return __varmap;
            }
            inline const std::map<std::string,pformula>& varmap() const{
                return __varmap;
            }

            // inline std::map<std::string,std::string>& set_info(){
            //     return __set_info;
            // }

            inline void add_set_info(const std::string& s1,std::string s2)
            {
                this->__set_info[s1]=std::move(s2);
            }
            inline const std::map<std::string,std::string>&
            set_info() const{
                return this->__set_info;
            }
            inline std::map<std::string,std::string>&
            set_info() {
                return this->__set_info;
            }
            inline const std::string & get_info(const std::string& s1) const
            {
                auto p=this->set_info().find(s1);
                if (p!=this->set_info().end())
                {
                    return p->second; 
                }
                static const std::string es=""; 
                return es;
            }


            inline bool var_contains(std::string v) const{
                return  this->varmap().find(v)!=this->varmap().end();
            }
            inline void add_varmap(std::string v,pformula f)
            {
                this->__varmap[v]=f;
            }
            inline void add_var(std::string v,std::string t)    
            {
                if (!this->var_contains(v))
                {
                    if (this->var_rename())
                    {
                        static const std::string svar="var";
                        this->__vars.push_back(std::make_shared<formula_var>(svar+std::to_string(this->__vars.size()),std::move(t)));        
                    }
                    else{
                        this->__vars.push_back(std::make_shared<formula_var>(v,std::move(t)));        
                    }
                    this->__varmap[v]=this->__vars.back();
                }

            }
            pformula& get_var(std::string v){
                auto ptr=this->varmap().find(v);
                if (ptr==this->varmap().end())
                {
                    throw std::invalid_argument("smtlib: 未知变量: "+v);
                }
                return ptr->second;
            }
            const pformula& get_var(std::string v) const {
                auto ptr=this->varmap().find(v);
                if (ptr==this->varmap().end())
                {
                    throw std::invalid_argument("smtlib: 未知变量: "+v);
                }
                return ptr->second;
            }
            // inline void add_set_info(std::string name,std::string info)
            // {
            //     this->__set_info[name]=info;
            // }
            inline void add_assert_list(pformula f)
            {
                this->__assert_list.push_back(std::move(f));
            }
            inline const std::vector<pformula>& 
            assert_list() const{
                return __assert_list;
            }
            friend std::ostream& operator<<  (std::ostream& stream, const smtlib& v);
        };

        smtlib read_smtlib2(smtlib2_read& smt2, bool is_var_rename=false);
        inline smtlib read_smtlib2(std::string s, bool is_var_rename=false)
        {
            std::ifstream smt2_f(s);
            if (!smt2_f.is_open())
            {
                throw std::invalid_argument("read_smtlib2: 无法打开文件 "+s);
                // return smtlib();
            }
            smtlib2_read smt2(&smt2_f);
            return read_smtlib2(smt2,is_var_rename);
        }        
        
    }
    


}

#endif