/**
 * @file formula.hh
 * @author haokun li (ker@pm.me)
 * @brief 
 * @version 0.1
 * @date 2022-10-25
 * 
 * @copyright Copyright (c) 2022
 * 
 */
#ifndef SMT_FORMULA_HH
#define SMT_FORMULA_HH
#include <string>
#include <vector>
// #include <clpoly/clpoly.hh>
#include <iostream>
#include <sstream>
#include <set>
#include <memory>
namespace smt{
    class formula;
    using pformula=std::shared_ptr<formula>;
    
    class formula
    {
        private:
            std::string __head;
            std::vector<pformula> __ele;
            std::size_t __data;
        public:
            typedef typename std::vector<pformula>::iterator iterator;
            typedef typename std::vector<pformula>::const_iterator  const_iterator ;

            inline formula()
            :__head(),__ele(),__data(0)
            {
                // std::cout<<"formula start.\n";
            
            }
            inline formula(std::string head)
            :__head(std::move(head)),__ele(),__data(0)
            {
                // std::cout<<"formula start.\n";
            
            }
            inline formula(std::string head,std::vector<pformula> e)
            :__head(std::move(head)),__ele(std::move(e)),__data(0)
            {
                // std::cout<<"formula start.\n";
            
            }
            virtual ~formula(){
                // std::cout<<"formula end.\n";
            }
            
            const std::string& head() const{
                return this->__head;
            }
            
            const std::vector<pformula>& elements() const
            {
                return this->__ele;
            }

            inline auto size() const {return this->__ele.size();}
            inline iterator begin() {return this->__ele.begin();}
            inline const_iterator  begin() const {return this->__ele.begin();}
            inline iterator  end() {return this->__ele.end();}
            inline const_iterator  end() const {return this->__ele.end();}
            inline pformula& front() {return this->__ele.front();}
            inline const pformula& front() const {return this->__ele.front();}
            inline pformula& back() {return this->__ele.back();}
            inline const pformula& back() const {return this->__ele.back();}
            inline void resize(std::size_t size){this->__ele.resize(size);}
            inline void reserve(std::size_t size){this->__ele.reserve(size);}
            inline void pop_back(){this->__ele.pop_back();}
            inline void push_back(const pformula&  value ){this->__ele.push_back(value);}
            inline void push_back(pformula&&  value){this->__ele.push_back(std::move(value));}
            inline pformula& operator[](std::size_t pos){return this->__ele[pos];}
            inline const pformula& operator[](std::size_t pos) const {return this->__ele[pos];}
            inline pformula& at(std::size_t pos){return this->__ele.at(pos);}
            inline const pformula& at(std::size_t pos) const {return this->__ele.at(pos);}
            inline bool empty() const{return this->__ele.empty();}

            
            virtual std::ostream& sstream(std::ostream& ss) const{
                if (!this->head().empty())
                {
                    ss<<"("<<this->head();
                    for (auto i=this->begin();i!=this->end();++i)
                    {
                        if (i!=this->begin())
                            ss<<" ";
                        (*i)->sstream(ss);

                    } 
                    ss<<")";
                }
                return ss;
            }
            std::string str() const{
                std::stringstream ss;
                this->sstream(ss);
                return ss.str();
            }

            inline size_t& data(){
                return __data;
            }
            inline const size_t& data() const {
                return __data;
            }
            
    };
    inline std::ostream& operator<<  (std::ostream& stream, const formula& v) 
    {
        v.sstream(stream);
        return stream;
    }
    inline std::ostream& operator<<  (std::ostream& stream, const pformula& v) 
    {
        v->sstream(stream);
        return stream;
    }
    class formula_var:public formula
    {
        private:
            std::string __var;
            std::string __thory;

        public:
            formula_var(std::string name, std::string thory)
            :formula("var"),__var(std::move(name)),__thory(std::move(thory))
            {
                // std::cout<<"formula_var start.\n";
            }
            virtual ~formula_var(){
                // std::cout<<"formula_var end.\n";
            }

            virtual std::ostream& sstream(std::ostream& ss) const{
                ss<<this->__var<<"@"<<__thory;
                return ss;
            }
            
            const std::string & var_name() const{
                return __var;
            }
            const std::string & var_thory() const{
                return __thory;
            }

    };

    class formula_num:public formula
    {
        private:
            std::string __num;

        public:
            
            formula_num(std::string n)
            :formula("num"),__num(std::move(n))
            {
                // std::cout<<"formula_num start.\n";
            }

            virtual ~formula_num(){
                // std::cout<<"formula_num end.\n";
            }

            virtual std::ostream& sstream(std::ostream& ss) const{
                ss<<this->__num;
                return ss;
            }

    };

    inline bool is_formula_op(const std::string& s)
    {
        static const std::set<std::string> op_l=
        {"+","-","*","/","and","or","not",">","<","<=",">=","="};
        return (op_l.find(s)!=op_l.end());
            
    }
    inline bool is_formula_var(const pformula& f)
    {
        return f->head()=="var";
    }
    inline bool is_formula_num(const pformula& f)
    {
        return f->head()=="num";
    }
    pformula formula_not(const pformula& f);
   
    using pformula_num=std::shared_ptr<formula_num>;
    using pformula_var=std::shared_ptr<formula_var>;
    
}
    
    
#endif