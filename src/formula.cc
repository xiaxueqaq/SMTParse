/**
 * @file formula.cc
 * @author haokun li (ker@pm.me)
 * @brief 
 * @version 0.1
 * @date 2022-10-26
 * 
 * @copyright Copyright (c) 2022
 * 
 */
#include "formula.hh"
#include <map>
namespace smt{
    pformula formula_not(const pformula& f)
    {
        if (f->head()=="var")
        {
            formula_var* fv=(formula_var*)f.get();
            if (fv->var_thory()!="bool")
                throw std::invalid_argument("formula_not 非 bool var");        
            return std::make_shared<formula>("not",std::vector<pformula>({f}));
        }
        if (!is_formula_op(f->head()))
        {
            throw std::invalid_argument("formula_not 未知head");
        }
        static const std::map<std::string,std::string> oppair1=
        {
            {"and","or"},
            {"or","and"},
        };
        static const std::map<std::string,std::string> oppair2=
        {
            {">","<="},
            {"<",">="},
            {">=","<"},
            {"<=",">"}
        };
        {
            auto ptr=oppair1.find(f->head());
            if (ptr!=oppair1.end())
            {
                std::vector<pformula> tmp;
                for (auto& i:*f)
                {
                    tmp.push_back(formula_not(i));
                }
                return std::make_shared<formula>(ptr->second,std::move(tmp));
            }
        }
        {
            auto ptr=oppair2.find(f->head());
            if (ptr!=oppair2.end())
            {
                        return std::make_shared<formula>(ptr->second,f->elements());
            }
        }
        if (f->head()=="not")
        {
            return f->elements().front();
        }
        if (f->head()=="=")
        {
            return std::make_shared<formula>("or",std::vector<pformula>({
                std::make_shared<formula>(">",f->elements()),
                std::make_shared<formula>("<",f->elements())
            }));
        }
        return f;
    }

}