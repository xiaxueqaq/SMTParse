/**
 * @file nra_analyze.cc
 * @author lihaokun (ker@pm.me)
 * @brief 
 * @version 0.1
 * @date 2022-10-26
 * 
 * @copyright Copyright (c) 2022
 * 
 */

#include "nra_analyze.hh"
namespace smt{
    namespace NRA{
        
        std::string boolvartorealvar_name(const std::string & s)
        {
            return s+"__boolvar";
        }
        
        std::shared_ptr<formula_var> boolvartorealvar(const std::shared_ptr<formula_var>& f)
        {
            return std::make_shared<formula_var>(boolvartorealvar_name(f->var_name()),"real");
        }

        clpoly::polynomial_ZZ formula_to_polyZ(const pformula& f);
        bool is_simple_poly(const clpoly::polynomial_ZZ & p )
        {
            for (auto& i:p.variables())
            {
                if (i.second>1)
                    return false;
            }
            return true;
        }
        
        NRA_CNF::NRA_CNF(const std::vector<std::vector<std::pair<clpoly::polynomial_ZZ,char>>>& data, bool is_no_unsimple_eq)
        {
            this->__is_exist_unsimpleeq=false;
            static const std::map<char,int> cmap={{'<',0},{'=',1},{'>',2}};
            for(auto& i:data)
            {
                this->__cnf.push_back(std::vector<std::pair<size_t,char>>());
                std::set<size_t> s;
                for(auto&j:i)
                {
                    if (clpoly::is_number(j.first))
                    {
                        const auto& nn=j.first.empty()?0:j.first.front().second;
                        bool mode=false;
                        switch (j.second)
                        {
                        case '=':
                            mode=(nn==0);
                            break;
                        case '<':
                            mode=(nn<0);
                            break;
                        case '>':
                            mode=(nn>0);
                            break;
                        
                        default:
                            throw std::invalid_argument("NRA_CNF 非法参数");
                        }
                        if (mode)
                            this->__cnf.pop_back();
                        continue;
                    }
                    if (is_no_unsimple_eq && j.second=='=' && !is_simple_poly(j.first) )
                    {
                        this->__is_exist_unsimpleeq=true;
                        continue;
                    }
                    size_t index=this->get_polyz(j.first);
                    auto ptr=cmap.find(j.second);
                    if (ptr==cmap.end())
                        throw std::invalid_argument("NRA_CNF 非法参数");
                    size_t h=index*3+ptr->second;
                    if (s.find(h)==s.end()){
                        s.insert(h);
                        if (s.find(index*3)!=s.end() &&
                            s.find(index*3+1)!=s.end() &&
                            s.find(index*3+2)!=s.end() )
                        {
                            this->__cnf.pop_back();
                            break;
                        }
                        this->__cnf.back().push_back({index,j.second});
                    }
                }
                if (this->__cnf.size()!=0 && this->__cnf.back().empty())
                {
                    this->__cnf.clear();
                    break;
                }    
            }
        }
        NRA_CNF::NRA_CNF(const std::vector<std::vector<std::pair<pformula,char>>>& data, bool is_no_unsimple_eq)
        {
            this->__is_exist_unsimpleeq=false;
            static const std::map<char,int> cmap={{'<',0},{'=',1},{'>',2}};
            // std::unordered_map<pformula,size_t> fpmap;
            for(auto& i:data)
            {
                this->__cnf.push_back(std::vector<std::pair<size_t,char>>());
                std::set<size_t> s;
                for(auto&j:i)
                {
                    auto op=j.second;
                    size_t index=0;
                    {
                        // auto ptr=fpmap.find(j.first);
                        if (j.first->data()){  
                            index=(j.first->data()>>1)-1;
                            if (j.first->data()& 1){
                                if (op=='<')    op='>';
                                else if (op=='>')    op='<';
                            }
                        }else{
                            auto p=formula_to_polyZ(j.first);
                            if (clpoly::is_number(p))
                            {
                                const auto& nn=p.empty()?0:p.front().second;
                                bool mode=false;
                                switch (op)
                                {
                                case '=':
                                    mode=(nn==0);
                                    break;
                                case '<':
                                    mode=(nn<0);
                                    break;
                                case '>':
                                    mode=(nn>0);
                                    break;
                                
                                default:
                                    throw std::invalid_argument("NRA_CNF 非法参数");
                                }
                                if (mode)
                                    this->__cnf.pop_back();
                                continue;
                            }
                            int tmp=0;
                            if (!p.empty() && p.front().second<0)
                            {                
                                p=-p;
                                if (op=='<')    op='>';
                                else if (op=='>')    op='<';
                                tmp=1;
                            }
                            index=this->get_polyz(p);
                            j.first->data()=((index+1)<<1)+tmp;
                        }
                    }
                    if (is_no_unsimple_eq && op=='=' && !is_simple_poly(this->polyz(index)) )
                    {
                        this->__is_exist_unsimpleeq=true;
                        continue;
                    }
                    size_t h=0;
                    {
                        auto ptr=cmap.find(op);
                        if (ptr==cmap.end())
                            throw std::invalid_argument("NRA_CNF 非法参数");
                        h=index*3+ptr->second;
                    }
                    if (s.find(h)==s.end()){
                        s.insert(h);
                        if (s.find(index*3)!=s.end() &&
                            s.find(index*3+1)!=s.end() &&
                            s.find(index*3+2)!=s.end() )
                        {
                            this->__cnf.pop_back();
                            break;
                        }
                        this->__cnf.back().push_back({index,op});
                    }
                }
                if (this->__cnf.size()!=0 && this->__cnf.back().empty())
                {
                    this->__cnf.clear();
                    break;
                }    
            }
        }
        std::ostream& ZZ_to_smt2(std::ostream& stream,const clpoly::ZZ & z)
        {
            if (z>=0)
                stream<<z;
            if (z<0)
                stream<<"(- 0 "<<-z<<")";
            return stream;
        }
        std::ostream& polynomial_to_smt2(std::ostream& stream,const clpoly::polynomial_ZZ & p)
        {
            if (p.empty())
                stream<<"0";
            if (p.size()!=1)
                stream<<"(+ ";
            for (auto & i:p)
            {
                if(i.first.empty())
                    ZZ_to_smt2(stream,i.second);
                else{
                    stream<<"(* ";
                    ZZ_to_smt2(stream,i.second);
                    stream<<" ";
                    for (auto &j:i.first)
                    {
                        for (auto d=0;d<j.second;++d)
                        {
                            stream<<j.first<<" ";
                        }
                    }
                    stream<<" )";
                }
                stream<<" ";
            }
            if (p.size()!=1)
                stream<<")";
            return stream;
        }
        std::ostream& NRA_CNF::to_smt2(std::ostream& stream,const std::string& s) const
        {
            stream<<"(set-info :smt-lib-version 2.6)"<<std::endl;
            stream<<"(set-logic QF_NRA)"<<std::endl;
            stream<<"(set-info :source |"<<std::endl<<s<<std::endl<<"|)"<<std::endl;
            stream<<"(set-info :category \"random\")"<<std::endl;
            stream<<"(set-info :status unknown)"<<std::endl;
            for (auto& v:this->vars())
            {
                stream<<"(declare-fun "<<v<<" () Real)"<<std::endl;
            }
            if (!this->__cnf.empty())
            {
                stream<<"(assert (and"<<std::endl;
                for (auto& C:this->__cnf)
                {
                    if (!C.empty())
                    {
                        stream<<"  (or "<<std::endl;
                        for(auto& a:C)
                        {
                            stream<<"    ("<<a.second<<" ";
                            polynomial_to_smt2(stream,this->polyz(a.first));
                            stream<<" 0 )"<<std::endl;
                        }
                        stream<<")"<<std::endl;
                    }
                }
                stream<<"))"<<std::endl;
            }
            stream<<"(check-sat)"<<std::endl;
            stream<<"(exit)"<<std::endl;
            return stream;
        }
        std::ostream& NRA_CNF::to_maple(std::ostream& stream,const std::string& s) const
        {
            stream<<"[\n";
            stream<<"  [\""<<s<<"\"],\n";
            static const std::map<char,int> opm={
                {'<',-1},
                {'=',0},
                {'>',1}
            };
            stream<<"  [";
            for (auto p=this->__polys.begin();p!=this->__polys.end();++p)
            {
                if (p!=this->__polys.begin())
                {
                    stream<<",";
                }
                stream<<*p;
            }
            stream<<"],\n";
            stream<<"  [\n";
            for (auto p=this->__cnf.begin();p!=this->__cnf.end();++p)
            {
                if (p!=this->__cnf.begin())
                {
                    stream<<",\n";
                }
                stream<<"    [";
                for (auto p1=p->begin();p1!=p->end();++p1)
                {
                    if (p1!=p->begin())
                    {
                        stream<<",";
                    }
                    stream<<"["<<(p1->first+1)<<","<<opm.at(p1->second)<<"]";
                }
                stream<<"]";
            }
            stream<<"\n  ],\n";
            stream<<"  [";
            for (auto p=this->__vars.begin();p!=this->__vars.end();++p)
            {
                if (p!=this->__vars.begin())
                {
                    stream<<",";
                }
                stream<<*p;
            }
            stream<<"]\n";
            
            stream<<"]\n";
            
            return stream;
        }

        NRA_CNF NRA_CNF::random(
            std::pair<uint,uint> variable_num,
            std::pair<uint,uint> polynomial_num,
            std::pair<uint,uint> polynomial_deg,
            std::pair<uint,uint> polynomial_var_num,
            // T_dens p_dens,
            std::pair<uint,uint> polynomial_len,
            std::pair<uint,uint> clause_num,
            std::pair<uint,uint> clause_len,
            bool is_exist_unsimpleeq,
            bool is_exist_neq)
        {
            NRA_CNF ans;
            ans.__is_exist_unsimpleeq=is_exist_unsimpleeq;
            std::random_device rd;
            std::mt19937_64 gen(rd());
            std::bernoulli_distribution rand2(0.5);
            int var_num=std::uniform_int_distribution<>(variable_num.first,variable_num.second)(gen);
            // std::cout<<"var_num :"<<var_num<<std::endl;
            // std::uniform_int_distribution<> var_gen(0,var_num-1);
            std::vector<clpoly::variable> var_l;
            for (int i=0;i<var_num;++i)
            {
                clpoly::variable v("x"+std::to_string(i));
                ans.__vars.insert(v);
                var_l.push_back(v);
            }
            int poly_num=std::uniform_int_distribution<>(polynomial_num.first,polynomial_num.second)(gen);
            // std::cout<<"poly_num :"<<poly_num<<std::endl;
            std::uniform_int_distribution<> poly_deg_r(polynomial_deg.first,polynomial_deg.second);
            std::uniform_int_distribution<> poly_var_num_r(polynomial_var_num.first,polynomial_var_num.second);
            std::uniform_int_distribution<> poly_len_r(polynomial_len.first,polynomial_len.second);                                 
            for (int i=0;i<poly_num;++i)
            {
                int poly_deg=poly_deg_r(gen);
                int poly_var_num=poly_var_num_r(gen);
                int poly_len=poly_len_r(gen);
                std::vector<clpoly::variable> poly_v;
                auto tmp_l=clpoly::random_select(var_num,poly_var_num,true);
                for(int j=0;j<tmp_l.size();++j)
                {
                    // std::cout<<tmp_l[j]<<" ";
                    assert(0<=tmp_l.at(j) &&tmp_l.at(j)<var_num );
                    poly_v.push_back(var_l[tmp_l[j]]);
                }
                // std::cout<<std::endl<<poly_v<<std::endl;
                // double p=p_dens(poly_deg,poly_var_num);
                // std::cout<<p<<std::endl;
                // auto t=clock();
                clpoly::polynomial_ZZ poly=clpoly::random_polynomial<clpoly::ZZ>(poly_v,poly_deg,poly_len,{1000,-1000},true);
                if (clpoly::is_number(poly)) continue;
                // std::cout<<"poly"<<i<<" : "<<poly<<std::endl;
                // std::cout<<poly_deg<<" "<<poly_var_num<<" "<<(((double)clock()-t)/CLOCKS_PER_SEC)<<"s"<<std::endl;
                
                ans.get_polyz(std::move(poly));
            }
            poly_num=ans.polys().size();
            if (poly_num==0)
                return ans;
            int c_num=std::uniform_int_distribution<>(clause_num.first,clause_num.second)(gen);
            std::uniform_int_distribution<> c_len_r(clause_len.first,clause_len.second);
            std::uniform_int_distribution<> poly_gen(0,poly_num*3-1);
            
            for (int i=0;i<c_num;++i)
            {
                int c_len=c_len_r(gen);
                if (c_len)
                {
                    ans.__cnf.push_back(std::vector<std::pair<size_t,char>>());
                    std::set<size_t> s;
                    auto tmp_l=clpoly::random_select(poly_num*3,c_len,true);
                    for(int j=0;j<tmp_l.size();++j)
                    {
                        assert(0<=tmp_l.at(j) &&tmp_l.at(j)<poly_num*3 );
                        int tmp=tmp_l.at(j);
                        size_t poly_index=tmp/3;
                        char op;
                        switch (tmp % 3)
                        {
                        case 0:
                            op='<';
                            break;
                        case 1:
                            op='=';
                            break;
                        case 2:
                            op='>';
                            break;
                        }
                        // std::cout<<tmp<<" "<<poly_index<<" "<<op<<std::endl;
                        if (op=='=' && !is_simple_poly(ans.polyz(poly_index)) 
                                && !is_exist_unsimpleeq)
                        {
                            if (rand2(gen))
                            {
                                op='>';
                            }
                            else{
                                op='<';
                            }
                        }
                        if (s.find(tmp)!=s.end())
                        {
                            continue;
                        }
                        s.insert(tmp);
                        if (s.find(poly_index*3)!=s.end() &&
                            s.find(poly_index*3+1)!=s.end() &&
                            s.find(poly_index*3+2)!=s.end() )
                        {
                            continue;    
                        }
                        if (!is_exist_neq && op!='=' &&
                            (s.find(poly_index*3)!=s.end() && s.find(poly_index*3+2)!=s.end()))
                        {
                            continue;    
                        }
                        ans.__cnf.back().push_back({poly_index,op});
                        // std::cout<<ans.polyz(poly_index)<<op<<"0"<<" || ";
                    }
                    if   (ans.__cnf.empty())
                        ans.__cnf.pop_back();
                    // std::cout<<std::endl;
                }

            }
            // std::cout<<ans.__vars.size()<<std::endl;
            return ans;
        }
        // double poly_assign(const std::map<clpoly::variable,double>& X,const std::)
        // {

        // }
        // double NRA_CNF::assign(const std::map<clpoly::variable,double>& X, double dl_B,double dl_o,double deq_B)
        // {
        //     double ans=0;
        //     for (auto &i:this->__cnf)
        //     {
        //         double tmp=1;
        //         for (auto &j:i)
        //         {
        //             switch (j.second)
        //             {
        //             case '<':
        //                 if 
        //                 break;
                    
        //             default:
        //                 break;
        //             }
        //         }
        //         ans+=tmp;
        //     }    
        // }

        std::ostream& operator<<  (std::ostream& stream, const NRA_CNF& C)
        {
            for(auto p1=C.__cnf.begin();p1!=C.__cnf.end();++p1)
            {
                if (p1!=C.__cnf.begin())
                    stream<<"&& ";
                stream<<" ( ";
                for(auto p2=p1->begin();p2!=p1->end();++p2)
                {
                    if (p2!=p1->begin())
                        stream<<" || ";
                    stream<<C.polyz(p2->first)<<p2->second<<"0";
                }
                stream<<" ) "; 
            }
            return stream;
        }
        bool is_boolformula(const pformula& f)
        {
            static const std::set<std::string> op_l=
            {"=","<",">","<=",">=","and","or","not"};
            if (op_l.find(f->head())!=op_l.end())
            {
                return true;
            }
            if (f->head()=="var" && ((formula_var*)f.get())->var_thory()=="bool")
            {
                return true;
            }
            return false;
        }
        
        bool is_poly(const pformula& f)
        {
            static const std::set<std::string> op_l=
            {"+","-","*","/"};
            if (op_l.find(f->head())!=op_l.end())
            {
                for (auto &i:f->elements())
                {
                    if (!is_poly(i))
                    {
                        return false;
                    }
                }
                return true;
            }
            if (f->head()=="var" && ((formula_var*)f.get())->var_thory()=="real")
            {
                return true;
            }
            return false;
        }
        
        clpoly::polynomial_QQ formula_var_to_polyQ(const pformula& f)
        {
            if (is_formula_var(f))
            {
                if (((formula_var*)f.get())->var_thory()!="real")
                {
                    throw std::invalid_argument("formula_var_to_polyQ 非 poly");
                }
                return clpoly::variable(((formula_var*)f.get())->var_name());
            }
            return clpoly::polynomial_QQ();
        }
        bool is_booleq(const pformula&f)
        {
            return  f->head()=="=" && f->size()==2 && is_boolformula(f->at(0)) && is_boolformula(f->at(1));
        }
        pformula formula_nbooleq(const pformula&f)
        {
            return std::make_shared<formula>("and",std::vector<pformula>({
                    std::make_shared<formula>("or",std::vector<pformula>({
                        std::make_shared<formula>("not",std::vector<pformula>({f->at(0)})),
                        f->at(1)
                    })),
                    std::make_shared<formula>("or",std::vector<pformula>({
                        std::make_shared<formula>("not",std::vector<pformula>({f->at(1)})),
                        f->at(0)
                    }))
                }));
        }
        clpoly::polynomial_QQ formula_num_to_polyQ(const pformula& f)
        {
            if (is_formula_num(f))
            {
                const std::string& s=f->str();
                clpoly::QQ q=0;
                clpoly::QQ p=1;
                int mode=0;
                for (auto c:s)
                {
                    if (c=='.')
                        mode=1;
                    else{
                        if (!(c<='9' && c>='0'))
                            throw std::invalid_argument("formula_num_to_QQ error: not number");
                        q=q*10+c-'0';
                        if (mode)
                            p*=10;
                    }
                }
                return {{{},q/p}};
            }
            return  clpoly::polynomial_QQ();
        }
        clpoly::polynomial_QQ formula_mult_to_polyQ(const pformula& f)
        {
            auto ptr=f->begin();
            if (ptr==f->end())
                throw std::invalid_argument("formula_mult_to_polyQ: 缺少参数");
            clpoly::polynomial_QQ p=formula_to_polyQ(*(ptr++));
            for(;ptr!=f->end();++ptr)
            {
                clpoly::polynomial_QQ p1=formula_to_polyQ(*ptr);
                p=p*p1;
            }
            return p;
        }
        clpoly::polynomial_QQ formula_div_to_polyQ(const pformula& f)
        {
            if (f->elements().size()!=2)
                throw std::invalid_argument("formula_div_to_polyQ: 参数错误");
            clpoly::polynomial_QQ p1=formula_to_polyQ(f->elements()[0]);
            clpoly::polynomial_QQ p2=formula_to_polyQ(f->elements()[1]);
            if (clpoly::is_number(p1) && clpoly::is_number(p2))
            {
                return p1/p2;
            }
            else 
            {
                if(clpoly::is_number(p2)){
                    clpoly::QQ p2_q=p2.empty()?0:p2.front().second;
                    if (p2_q)
                    {
                        for (auto& i:p1)
                        {
                            i.second/=p2_q;
                        }
                        return p1;
                    }
                    else{
                        throw std::invalid_argument("formula_div_to_polyQ: 除0");
                    }

                }
                else{
                        throw std::invalid_argument("formula_div_to_polyQ: 多项式除法");    
                }
            }
        }
        clpoly::polynomial_QQ formula_add_to_polyQ(const pformula& f)
        {
            auto ptr=f->begin();
            if (ptr==f->end())
                throw std::invalid_argument("formula_add_to_polyQ: 缺少参数");
            clpoly::polynomial_QQ p=formula_to_polyQ(*(ptr++));
            for(;ptr!=f->end();++ptr)
            {
                clpoly::polynomial_QQ p1=formula_to_polyQ(*ptr);
                p=p+p1;
            }
            return p;
        }
        clpoly::polynomial_QQ formula_sub_to_polyQ(const pformula& f)
        {
            auto ptr=f->begin();
            if (ptr==f->end())
                throw std::invalid_argument("formula_sub_to_polyQ: 缺少参数");
            clpoly::polynomial_QQ p=formula_to_polyQ(*(ptr++));
            if (ptr==f->end())
            {
                return -p;
            }
            for(;ptr!=f->end();++ptr)
            {
                clpoly::polynomial_QQ p1=formula_to_polyQ(*ptr);
                p=p-p1;
            }
            return p;
        }
        
        const std::map<std::string,std::function<clpoly::polynomial_QQ(const pformula&)>> formula_to_polyQ_l=
        {
             {"num",formula_num_to_polyQ}
            ,{"var",formula_var_to_polyQ}
            ,{"*"  ,formula_mult_to_polyQ}
            ,{"/"  ,formula_div_to_polyQ}
            ,{"+"  ,formula_add_to_polyQ}
            ,{"-"  ,formula_sub_to_polyQ}
        };
        
        clpoly::polynomial_QQ formula_to_polyQ(const pformula& f)
        {
            std::string head=f->head();
            auto fun_p=formula_to_polyQ_l.find(head);
            if (fun_p!=formula_to_polyQ_l.end())
            {
                return fun_p->second(f);
            }
            else{
                throw std::invalid_argument("formula_to_polyQ 未知");
            }
        }
        clpoly::polynomial_ZZ formula_to_polyZ(const pformula& f)
        {
            auto p1=formula_to_polyQ(f);
            clpoly::polynomial_ZZ p2;
            clpoly::poly_convert(p1,p2);
            return p2;
        }
        
        std::pair<clpoly::polynomial_ZZ,char> formula_to_polyzop(const pformula&f)
        {
            char op=0;
            if (f->head()=="<" || f->head()=="=" || f->head()==">" )
                op=f->head().front();
            else
                throw std::invalid_argument("formula_to_polyzops 未知符号");
            if (f->size()!=2)
                throw std::invalid_argument("formula_to_polyzops 长度错误");
            auto p1=formula_to_polyQ(f->elements()[0]);
            auto p2=formula_to_polyQ(f->elements()[1]);
            clpoly::polynomial_ZZ p;
            clpoly::poly_convert(p1-p2,p);
            if (!p.empty() && p.front().second<0)
            {
                p=-p;
                if (op=='<')    op='>';
                else if (op=='>')    op='<';
            }
            return {p,op};            
        }
        std::vector<std::pair<clpoly::polynomial_ZZ,char>> formula_to_polyzops(const pformula&f)
        {
            if (f->head()=="var")
            {
                formula_var* fv=(formula_var*)f->at(0).get();
                if (fv->var_thory()!="bool")
                    throw std::invalid_argument("formula_to_polyzops 非 bool var");        
                clpoly::variable v(boolvartorealvar_name(fv->var_name()));
                clpoly::polynomial_ZZ p=v;
                return  {{p,'>'}};
            }
            if (f->head()=="<=")
            {
                return {formula_to_polyzop(std::make_shared<formula>("<",f->elements())),
                        formula_to_polyzop(std::make_shared<formula>("=",f->elements()))
                };
            }
            if (f->head()==">=")
            {
                return {formula_to_polyzop(std::make_shared<formula>(">",f->elements())),
                        formula_to_polyzop(std::make_shared<formula>("=",f->elements()))
                };
            }
            if (f->head()=="<" || f->head()=="=" || f->head()==">")
                return {formula_to_polyzop(f)};
            throw std::invalid_argument("formula_to_polyzops 未知符号");
        }
        std::vector<std::vector<std::pair<clpoly::polynomial_ZZ,char>>> formula_var_to_cnf(const pformula&f)
        {
            if (f->head()=="var")
            {
                formula_var* fv=(formula_var*)f.get();
                if (fv->var_thory()!="bool")
                    throw std::invalid_argument("formula_var_to_cnf 非 bool var");        
                clpoly::variable v(boolvartorealvar_name(fv->var_name()));
                clpoly::polynomial_ZZ p=v;
                return  {{{p,'>'}}};
            
            }

            if(f->head()=="not" && f->size()==1 && f->at(0)->head()=="var")
            {

                formula_var* fv=(formula_var*)f->at(0).get();
                if (fv->var_thory()!="bool")
                    throw std::invalid_argument("formula_var_to_cnf 非 bool var");        
                clpoly::variable v(boolvartorealvar_name(fv->var_name()));
                clpoly::polynomial_ZZ p=v;
                return  {{{p,'<'},{p,'='}}};
            }
            throw std::invalid_argument("formula_var_to_cnf 异常分支");        
        }
        std::vector<std::vector<std::pair<clpoly::polynomial_ZZ,char>>> formula_not_to_cnf(const pformula&f)
        {
            assert(f->head()=="not");
            if (f->size()!=1)
                throw std::invalid_argument("formula_not_to_cnf 长度错误");
            if (f->at(0)->head()=="var")
            {
                return formula_var_to_cnf(f);
            }
            auto f1=formula_not(f->elements()[0]);
            return formula_to_cnf(f1);
        }
        std::vector<std::vector<std::pair<clpoly::polynomial_ZZ,char>>> formula_and_to_cnf(const pformula&f)
        {
            assert(f->head()=="and");
            if (f->size()==0)
                throw std::invalid_argument("formula_and_to_cnf 长度错误");
            auto ptr=f->begin();
            auto c1=formula_to_cnf(*(ptr++));
            for (;ptr!=f->end();)
            {
                auto c2=formula_to_cnf(*(ptr++));
                for (auto &i:c2)
                    c1.push_back(std::move(i));
            }
            return c1;
        }
        std::vector<std::vector<std::pair<clpoly::polynomial_ZZ,char>>> formula_or_to_cnf(const pformula&f)
        {
            assert(f->head()=="or");
            if (f->size()==0)
                throw std::invalid_argument("formula_or_to_cnf 长度错误");
            auto ptr=f->begin();
            auto c=formula_to_cnf(*(ptr++));
            for (;ptr!=f->end();)
            {
                auto c2=formula_to_cnf(*(ptr++));
                std::vector<std::vector<std::pair<clpoly::polynomial_ZZ,char>>> c1=std::move(c);
                c.clear();
                for (auto& i:c1)
                    for(auto& j:c2)
                    {
                        auto tmp=i;
                        for (auto& k:j)
                            tmp.push_back(k);
                        c.push_back(std::move(tmp));
                    }
            }
            return c;
        }

        const std::map<std::string,std::function< std::vector<std::vector<std::pair<clpoly::polynomial_ZZ,char>>>(const pformula&)>> ftc_l=
        {
             {"and",formula_and_to_cnf}
            ,{"or",formula_or_to_cnf}
            ,{"not"  ,formula_not_to_cnf}
            ,{"var", formula_var_to_cnf}
        };


        std::vector<std::pair<pformula,char>> formula_normal_op(const pformula&f)
        {
            auto p=std::make_shared<formula>("-",f->elements());
            if (f->head()=="<=")
            {
                return {{p,'<'},
                        {p,'='}
                       };
            }
            if (f->head()==">=")
            {
                return {{p,'>'},
                        {p,'='}
                       };
                        
            }
            if (f->head()=="<" || f->head()=="=" || f->head()==">")
                return {{p,f->head().front()}};
            throw std::invalid_argument("formula_normal_op 未知符号");
        }
        std::vector<std::vector<std::pair<pformula,char>>> formula_normal_var(const pformula&f)
        {
            if (f->head()=="var")
            {
                formula_var* fv=(formula_var*)f.get();
                if (fv->var_thory()!="bool")
                    throw std::invalid_argument("formula_normal_var 非 bool var");        
                pformula_var v=std::make_shared<formula_var>(boolvartorealvar_name(fv->var_name()),"real");
                return  {{{v,'>'}}};
            }

            if(f->head()=="not" && f->size()==1 && f->at(0)->head()=="var")
            {

                formula_var* fv=(formula_var*)f->at(0).get();
                if (fv->var_thory()!="bool")
                    throw std::invalid_argument("formula_normal_var 非 bool var");        
                pformula_var v=std::make_shared<formula_var>(boolvartorealvar_name(fv->var_name()),"real");
                return  {{{v,'<'},{v,'='}}};
            }
            throw std::invalid_argument("formula_normal_var 异常分支");        
        }
        std::vector<std::vector<std::pair<pformula,char>>> formula_normal_not(const pformula&f)
        {
            assert(f->head()=="not");
            if (f->size()!=1)
                throw std::invalid_argument("formula_normal_not 长度错误");
            if (f->at(0)->head()=="var")
            {
                return formula_normal_var(f);
            }
            auto f1=formula_not(f->elements()[0]);
            return formula_normal(f1);
        }
        std::vector<std::vector<std::pair<pformula,char>>> formula_normal_and(const pformula&f)
        {
            assert(f->head()=="and");
            if (f->size()==0)
                throw std::invalid_argument("formula_normal_and 长度错误");
            auto ptr=f->begin();
            auto c1=formula_normal(*(ptr++));
            for (;ptr!=f->end();)
            {
                auto c2=formula_normal(*(ptr++));
                for (auto &i:c2)
                    c1.push_back(std::move(i));
            }
            return c1;
        }
        std::vector<std::vector<std::pair<pformula,char>>> formula_normal_or(const pformula&f)
        {
            assert(f->head()=="or");
            if (f->size()==0)
                throw std::invalid_argument("formula_normal_or 长度错误");
            auto ptr=f->begin();
            auto c=formula_normal(*(ptr++));
            for (;ptr!=f->end();)
            {
                auto c2=formula_normal(*(ptr++));
                std::vector<std::vector<std::pair<pformula,char>>> c1=std::move(c);
                c.clear();
                for (auto& i:c1)
                    for(auto& j:c2)
                    {
                        auto tmp=i;
                        for (auto& k:j)
                            tmp.push_back(k);
                        c.push_back(std::move(tmp));
                    }
            }
            return c;
        }
        const std::map<std::string,std::function< std::vector<std::vector<std::pair<pformula,char>>>(const pformula&)>> fn_l=
        {
             {"and",formula_normal_and}
            ,{"or",formula_normal_or}
            ,{"not"  ,formula_normal_not}
            ,{"var", formula_normal_var}
        };
        std::vector<std::vector<std::pair<pformula,char>>> formula_normal(const pformula&f)
        {
            if (is_booleq(f))
            {
                return formula_normal(formula_nbooleq(f));
            }
            if (f->head()=="<" || f->head()=="=" || f->head()==">" || f->head()=="<=" || f->head()==">=" )
            {
                return {formula_normal_op(f)};
            }
            auto pfunc=fn_l.find(f->head());
            if (pfunc!=fn_l.end())
            {
                return pfunc->second(f);
            }
            throw std::invalid_argument("formula_normal 未知符号");
        }
        
        std::vector<std::vector<std::pair<clpoly::polynomial_ZZ,char>>> formula_to_cnf(const pformula&f)
        {

            if (is_booleq(f))
            {
                return formula_to_cnf(formula_nbooleq(f));
            }
            
            if (f->head()=="<" || f->head()=="=" || f->head()==">" || f->head()=="<=" || f->head()==">=" ){
                return {formula_to_polyzops(f)};
            }
            auto pfunc=ftc_l.find(f->head());
            if (pfunc!=ftc_l.end())
            {
                return pfunc->second(f);
            }
            throw std::invalid_argument("formula_to_cnf 未知符号"+f->head());
        }
        
        
        NRA_CNF smtlib_to_cnf(const smtlib::smtlib& l, bool is_no_unsimple_eq)
        {
            if (!is_nra_logic(l)) 
                throw std::invalid_argument("smtlib_to_cnf 不是nra");
            for(auto&i:l.vars())
            {
                if(i->var_thory()=="real"){
                    clpoly::variable::get_variable(i->var_name());
                }else{
                    clpoly::variable::get_variable(boolvartorealvar_name(i->var_name()));    
                }
            }
            auto f=std::make_shared<formula>("and",l.assert_list());
            {
                // auto t1=clock();
                auto tmp1=formula_normal(f);
                // std::cout<<"formula_normal time="<<double(clock()-t1)/CLOCKS_PER_SEC<<"s\n";
                // t1=clock();
                auto tmp2=NRA_CNF(tmp1,is_no_unsimple_eq);
                // std::cout<<"NRA_CNF time="<<double(clock()-t1)/CLOCKS_PER_SEC<<"s\n"; 
                return tmp2;
            }
            // // auto t=clock();
            // auto tmp=formula_to_cnf(std::make_shared<formula>("and",l.assert_list()));
            // // std::cout<<"formula_to_cnf time="<<double(clock()-t)/CLOCKS_PER_SEC<<"s\n"; 
            // // t=clock();
            // auto tmp2=NRA_CNF(tmp,is_no_unsimple_eq);
            // // std::cout<<"NRA_CNF time="<<double(clock()-t)/CLOCKS_PER_SEC<<"s\n"; 
            // return tmp2;
        }

        double assign_poly(const std::map<clpoly::variable,double>& X,const  clpoly::polynomial_ZZ& p)
        {
            double ans=0;
            for (auto & i:p)
            {
                double tmp=1;
                for (auto &j:i.first)
                {
                    tmp*=pow(X.at(j.first),j.second);
                }
                tmp*=i.second.get_d();
                ans+=tmp;
            }
            return ans;
        }
        // double assign_poly(const std::map<clpoly::variable,double>& X,size_t index)
        // {
        //     return assign_poly(X,this->polyz(index));
        // }

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
        double assign_op(const std::map<clpoly::variable,double>& X,double f,char op,double dl_B=0,double dl_a=0,double deq_B=0,double deq_a=0)
        {
            switch (op)
            {
            case '>':
                return (f>dl_B)? 0 :(f-dl_B)*(f-dl_B)+ dl_a;
                break;
            case '<':
                return (f<-dl_B)? 0 :(f+dl_B)*(f+dl_B)+ dl_a;
                break;
            case '=':
                return (f>deq_B)? (f-deq_B)*(f-deq_B)+ deq_a
                    :(
                        (f<-deq_B)?(f+deq_B)*(f+deq_B)+ deq_a:0
                    );
                break;        
            default:
                throw std::invalid_argument("assign_op 未知op "+std::string(1,op));
                break;
            }
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
        double NRA_CNF::assign(const std::map<clpoly::variable,double>& X, double dl_B,double dl_a,double deq_B,double deq_a)
        {
            std::vector<double> f_ans;
            f_ans.reserve(this->polys().size());
            for (auto & i:this->polys())
            {
                f_ans.push_back(assign_poly(X,i));
            }
            double ans=0;
            for (auto &i:this->__cnf)
            {
                double tmp=1;
                for (auto &j:i)
                {
                    tmp*=assign_op(X,f_ans[j.first],j.second,dl_B,dl_a,deq_B,deq_a);
                    if (tmp==0)
                        break;
                }
                ans+=tmp;
            }
            return ans;

        }

    }
}