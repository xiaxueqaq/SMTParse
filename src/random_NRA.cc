#include "nra_analyze.hh"
#include <algorithm>
#include <filesystem>
#include <time.h>

std::vector<std::string> init_cmd_option(int argc, char const *argv[])
{
    std::vector<std::string> arg;
    for (int i=1;i<argc;++i)
        arg.push_back(argv[i]);
    return arg;
}
bool cmd_option_exists(std::vector<std::string>& arg,std::string option)
{
    auto p=std::find(arg.begin(),arg.end(),option);
    return (p!=arg.end());
}
std::string get_cmd_option(std::vector<std::string>& arg,const std::string & option,const std::string& def="")
{
    auto p=std::find(arg.begin(),arg.end(),option);
    if (p!=arg.end() && (++p)!=arg.end())
    {
        return *p;
    }
    return def;
}
int get_cmp_option_int(std::vector<std::string>& arg,const std::string & option,int def=0)
{
    auto p=std::find(arg.begin(),arg.end(),option);
    if (p!=arg.end() && (++p)!=arg.end())
    {
        return std::stoi(*p);
    }
    return def;
}
int main(int argc, char const *argv[])
{
    std::vector<std::string> arg=init_cmd_option(argc,argv);
    // std::string file_name=get_cmd_option(arg,"-f");
    // bool is_rename=cmd_option_exists(arg,"--var_rename");
    // bool is_no_unsimple_eq=cmd_option_exists(arg,"--no_unsimple_eq");
    // bool is_no_unsat=cmd_option_exists(arg,"--no_unsat");
    std::string file_out_name=get_cmd_option(arg,"-o","random");
    int tnum=get_cmp_option_int(arg,"-n",1);
    int variable_num_down=get_cmp_option_int(arg,"--variable_num_down",20);
    int variable_num_up=get_cmp_option_int(arg,"--variable_num_up",30);
    std::cout<<"variable_num:"<<variable_num_down<<"-"<<variable_num_up<<std::endl;
    int polynomial_num_down=get_cmp_option_int(arg,"--polynomial_num_down",40);
    int polynomial_num_up=get_cmp_option_int(arg,"--polynomial_num_up",60);
    std::cout<<"polynomial_num:"<<polynomial_num_down<<"-"<<polynomial_num_up<<std::endl;
    int polynomial_deg_down=get_cmp_option_int(arg,"--polynomial_deg_down",20);
    int polynomial_deg_up=get_cmp_option_int(arg,"--polynomial_deg_up",30);
    std::cout<<"polynomial_deg:"<<polynomial_deg_down<<"-"<<polynomial_deg_up<<std::endl;
    int polynomial_var_num_down=get_cmp_option_int(arg,"--polynomial_var_num_down",8);
    int polynomial_var_num_up=get_cmp_option_int(arg,"--polynomial_var_num_up",12);
    std::cout<<"polynomial_var_num:"<<polynomial_var_num_down<<"-"<<polynomial_var_num_up<<std::endl;
    int polynomial_len_down=get_cmp_option_int(arg,"--polynomial_len_down",20);
    int polynomial_len_up=get_cmp_option_int(arg,"--polynomial_len_up",30);
    std::cout<<"polynomial_len:"<<polynomial_len_down<<"-"<<polynomial_len_up<<std::endl;
    int clause_num_down=get_cmp_option_int(arg,"--clause_num_down",20);
    int clause_num_up=get_cmp_option_int(arg,"--clause_num_up",40);
    std::cout<<"clause_num:"<<clause_num_down<<"-"<<clause_num_up<<std::endl;
    int clause_len_down=get_cmp_option_int(arg,"--clause_len_down",2);
    int clause_len_up=get_cmp_option_int(arg,"--clause_len_up",5);
    std::cout<<"clause_len:"<<clause_len_down<<"-"<<clause_len_up<<std::endl;
    // std::pair<uint,uint> variable_num,20,30
    // std::pair<uint,uint> polynomial_num,40,60
    // std::pair<uint,uint> polynomial_deg,20,30
    // std::pair<uint,uint> polynomial_var_num,8,12
    // // T_dens p_dens,
    // std::pair<uint,uint> polynomial_len,20,30
    // std::pair<uint,uint> clause_num,20,40
    // std::pair<uint,uint> clause_len,2,5
    smt::NRA::NRA_CNF cnf;
    for (int index=0;index<tnum;++index)
    {
            
        // cnf=smt::NRA::NRA_CNF::random(
        //     {20,30},
        //     {40,60},
        //     {10,20},
        //     {8,12},
        //     {10,20},
        //     {20,40},
        //     {2,5},
        //     false
        // );
        std::cout<<"生成 "<<file_out_name+std::to_string(index)<<" 开始"<<std::endl;
        cnf=smt::NRA::NRA_CNF::random(
            {variable_num_down,variable_num_up},
            {polynomial_num_down,polynomial_num_up},
            {polynomial_deg_down,polynomial_deg_up},
            {polynomial_var_num_down,polynomial_var_num_up},
            {polynomial_len_down,polynomial_len_up},
            {clause_num_down,clause_num_up},
            {clause_len_down,clause_len_up},
            false,false
        );
        {
            std::filesystem::path p(file_out_name+std::to_string(index)+".mpl");
            if (!p.parent_path().empty())
                        std::filesystem::create_directories(p.parent_path());
            std::ofstream o(p);
            if (!o.is_open()){
                throw std::invalid_argument("mpl 文件开启失败");
            }
            o<<"Eample:=";
            cnf.to_maple(o,file_out_name+std::to_string(index));
            o<<":";
            o.close();
        }
        {
            std::filesystem::path p(file_out_name+std::to_string(index)+".smt2");
            if (!p.parent_path().empty())
                    std::filesystem::create_directories(p.parent_path());
            std::ofstream o(p);
            if (!o.is_open()){
                throw std::invalid_argument("smt 文件开启失败");
            }
            cnf.to_smt2(o,file_out_name+std::to_string(index));
            o.close();
        }
         std::cout<<"生成 "<<file_out_name+std::to_string(index)<<" 完成"<<std::endl;
    }
    
    // {
    //     clpoly::variable x1("x1");
    //     clpoly::variable x2("x2");
    //     clpoly::variable x3("x3");
    //     clpoly::variable x4("x4");
    //     clpoly::variable x5("x5");
    //     clpoly::variable x6("x6");
    //     clpoly::variable x7("x7");
    //     clpoly::variable x8("x8");
    //     clpoly::variable x9("x9");
    //     clpoly::variable x10("x10");
    //     cnf.add_var(x1);
    //     cnf.add_var(x2);
    //     cnf.add_var(x3);
    //     cnf.add_var(x4);
    //     cnf.add_var(x5);
    //     cnf.add_var(x6);
    //     cnf.add_var(x7);
    //     cnf.add_var(x8);
    //     cnf.add_var(x9);
    //     cnf.add_var(x10);
    //     std::vector<clpoly::polynomial_ZZ> poly={-85*pow(x1,2)*pow(x10,2)*pow(x4,4)*pow(x5,3)*pow(x6,4)*pow(x7,3)*pow(x8,2)+66*x1*pow(x10,4)*x3*pow(x5,6)*x6*pow(x8,4)*pow(x9,3)+7*x1*x10*pow(x3,2)*pow(x4,3)*x5*x6*x7*pow(x8,5)*pow(x9,5)+54*pow(x10,4)*x2*x3*pow(x4,5)*x5*x6*x7*pow(x8,3)*pow(x9,3)-25*pow(x1,5)*pow(x10,2)*pow(x2,2)*pow(x4,5)*pow(x5,2)*x6*pow(x8,2)-77*pow(x1,2)*x2*x3*x4*pow(x5,6)*pow(x6,7)*x8-25*pow(x1,5)*pow(x5,6)*x7*pow(x8,2)*pow(x9,4)-98*x10*pow(x2,3)*pow(x3,3)*x5*x6*pow(x8,3)*pow(x9,5)-84*x10*x2*pow(x4,2)*pow(x5,2)*x7*pow(x8,4)*pow(x9,5)-13*pow(x4,5)*pow(x5,3)*pow(x7,3)*pow(x8,3)*x9, 
    //     -72*pow(x1,5)*x3*x4*pow(x5,4)*pow(x6,6)*pow(x7,3)+21*pow(x1,4)*pow(x2,6)*pow(x3,2)*pow(x4,4)*x5*pow(x6,2)*x8-72*pow(x1,3)*pow(x2,2)*pow(x4,9)*x5*pow(x6,3)*pow(x8,2)+50*pow(x1,2)*x10*pow(x2,3)*pow(x3,5)*pow(x5,2)*x6*pow(x9,6)+50*pow(x10,6)*x2*x3*pow(x4,2)*pow(x5,3)*pow(x7,4)*pow(x8,3)-96*pow(x10,3)*pow(x2,2)*pow(x4,3)*pow(x6,3)*pow(x7,5)*pow(x8,4)+19*pow(x1,3)*pow(x10,2)*pow(x4,3)*x5*pow(x6,3)*pow(x7,3)*pow(x8,2)*pow(x9,2)+30*pow(x1,2)*pow(x2,2)*x4*pow(x5,6)*pow(x7,4)*x8*pow(x9,2)-12*pow(x10,2)*pow(x4,4)*pow(x5,4)*pow(x8,7)-49*pow(x1,6)*x4*x5*x6*pow(x7,2)*x8*x9, 
    //     50*pow(x1,5)*pow(x10,3)*pow(x2,2)*pow(x3,5)*x4*pow(x8,3)*x9-14*pow(x1,2)*pow(x10,6)*pow(x2,2)*x4*pow(x5,6)*pow(x7,3)-47*pow(x1,2)*x2*x3*x4*pow(x7,12)*pow(x9,3)-34*pow(x10,3)*pow(x3,6)*x4*pow(x5,2)*pow(x6,3)*pow(x9,5)-98*pow(x10,2)*pow(x2,2)*pow(x4,2)*x5*pow(x6,3)*pow(x7,4)*pow(x8,3)*pow(x9,2)-43*x1*pow(x10,2)*pow(x2,4)*x3*pow(x4,2)*pow(x6,6)*x8*x9-73*pow(x3,2)*pow(x4,4)*pow(x5,4)*x6*x8*pow(x9,6)-54*pow(x1,4)*pow(x2,2)*x3*x6*pow(x7,6)*x8*pow(x9,2)+7*x10*pow(x3,7)*pow(x4,2)*pow(x5,2)*x6*x8*pow(x9,3)-52*pow(x2,5)*pow(x3,3)*pow(x4,2)*x6*pow(x7,2)*pow(x8,3), 
    //     -10*pow(x1,7)*x2*pow(x3,6)*pow(x5,2)*x6*pow(x8,2)*x9-7*x10*x2*pow(x3,10)*pow(x5,3)*pow(x7,2)*x8*pow(x9,2)-62*pow(x1,3)*pow(x10,4)*pow(x2,7)*pow(x4,3)*x5*x8+50*pow(x1,3)*x10*pow(x3,7)*x5*x7*pow(x8,6)-72*pow(x2,4)*pow(x3,4)*pow(x5,3)*x6*x7*pow(x9,6)-7*pow(x3,3)*pow(x4,5)*pow(x5,3)*pow(x6,5)*x8*x9-18*x10*pow(x2,3)*x3*pow(x4,2)*pow(x5,2)*pow(x6,6)*pow(x9,2)-86*x1*pow(x10,3)*pow(x4,7)*x6*pow(x9,4)-46*pow(x1,2)*pow(x10,3)*x2*pow(x3,3)*x5*pow(x8,5)-18*pow(x1,4)*pow(x10,2)*x3*x4*x6*x7*x8*x9, 
    //     9*pow(x1,5)*pow(x2,2)*x3*pow(x4,3)*pow(x5,4)*pow(x7,4)*x9-99*pow(x1,3)*pow(x10,3)*pow(x2,3)*x3*pow(x7,5)*pow(x8,5)+43*pow(x1,3)*pow(x2,3)*pow(x4,2)*pow(x5,4)*pow(x7,2)*pow(x8,5)*x9-61*pow(x10,2)*x2*pow(x3,5)*pow(x4,3)*x6*pow(x7,3)*pow(x8,2)*pow(x9,3)+88*pow(x2,5)*pow(x3,3)*pow(x6,7)*x7*pow(x9,4)-37*x1*pow(x3,2)*x4*pow(x6,5)*pow(x7,6)*pow(x8,3)*x9+28*x1*pow(x2,2)*pow(x3,5)*x4*pow(x5,7)*x7*x9-61*pow(x10,2)*pow(x4,3)*pow(x5,8)*x7*pow(x8,3)*x9-93*pow(x1,2)*x10*x2*pow(x3,3)*pow(x4,2)*pow(x5,3)*pow(x6,2)*pow(x7,2)*x9+22*pow(x2,7)*x3*pow(x4,3)*pow(x8,2)*x9, 
    //     -85*pow(x1,4)*pow(x10,5)*pow(x3,5)*pow(x4,2)*pow(x5,2)*x7*x8-13*pow(x1,2)*x10*pow(x2,7)*pow(x3,2)*pow(x4,3)*pow(x6,3)*x7*x9+13*x1*pow(x2,3)*pow(x3,5)*pow(x4,4)*pow(x5,3)*x7*pow(x8,3)-80*x10*x2*pow(x3,5)*x4*pow(x5,4)*pow(x7,4)*pow(x8,2)*pow(x9,2)-85*x1*x10*pow(x3,3)*pow(x4,3)*pow(x5,3)*pow(x6,6)*pow(x9,2)+73*pow(x10,3)*x2*pow(x3,6)*pow(x4,2)*pow(x6,2)*pow(x7,4)*x9+55*pow(x1,2)*pow(x10,4)*pow(x3,2)*x5*pow(x6,2)*x7*pow(x8,2)*pow(x9,4)-93*pow(x1,2)*x10*pow(x4,2)*pow(x5,10)*pow(x8,2)*x9+89*pow(x10,2)*pow(x2,4)*x5*pow(x6,2)*x7*pow(x9,6)+17*x10*x2*x3*x4*pow(x6,3)*x7*pow(x9,4), 
    //     -20*pow(x1,8)*x10*pow(x2,2)*x3*pow(x5,4)*pow(x6,3)*x8-62*pow(x1,3)*pow(x2,3)*pow(x3,2)*pow(x4,2)*x6*x7*pow(x8,5)*pow(x9,3)+11*pow(x1,3)*pow(x2,6)*pow(x4,3)*pow(x7,3)*pow(x8,2)*pow(x9,2)+11*pow(x1,2)*pow(x10,2)*x2*pow(x3,4)*x4*pow(x5,3)*pow(x7,3)*pow(x8,3)-59*x1*pow(x10,3)*x4*x6*pow(x7,8)*pow(x8,5)-4*pow(x1,5)*pow(x2,3)*x4*pow(x7,5)*pow(x8,4)+83*x1*pow(x3,2)*x4*x5*pow(x6,3)*pow(x7,6)*x8*pow(x9,3)+97*x10*pow(x4,2)*pow(x5,6)*x6*pow(x7,5)*pow(x8,2)*x9-78*x1*pow(x10,2)*x2*pow(x3,4)*pow(x4,2)*pow(x6,2)*pow(x8,4)*x9-96*x1*x2*x3*pow(x6,2)*x7*x8*pow(x9,7),
    //     5*pow(x1,9)*pow(x10,2)*x2*x3*x6*pow(x8,4)*pow(x9,2)-78*pow(x1,2)*pow(x2,4)*pow(x3,6)*x4*x5*x6*pow(x7,2)*pow(x9,3)-72*x1*pow(x10,3)*pow(x3,2)*pow(x5,5)*pow(x6,6)*x7*x8*x9-18*x1*pow(x10,3)*pow(x4,2)*x5*pow(x6,6)*pow(x7,5)*pow(x8,2)-2*x1*pow(x10,2)*x2*pow(x4,4)*pow(x6,3)*pow(x7,2)*pow(x9,7)+8*pow(x1,4)*pow(x2,2)*x3*x4*pow(x6,3)*pow(x8,5)*pow(x9,3)-92*pow(x1,4)*pow(x4,3)*x5*pow(x6,3)*pow(x7,3)*pow(x8,4)*x9-78*x1*pow(x10,2)*pow(x2,7)*pow(x3,2)*pow(x5,3)*x8*x9-99*x1*pow(x10,4)*x2*pow(x4,2)*pow(x5,4)*x7*x8*pow(x9,2)-26*x1*pow(x10,3)*pow(x3,4)*pow(x5,3)*x6*pow(x8,3), 
    //     -28*pow(x1,3)*x10*pow(x2,8)*x3*pow(x6,3)*pow(x7,4)-62*x1*pow(x10,8)*x2*pow(x4,6)*pow(x6,2)*x7*x9+71*x1*x2*pow(x3,2)*pow(x4,5)*pow(x5,5)*x6*x7*x8*pow(x9,3)-32*pow(x10,7)*pow(x2,2)*x3*x4*x5*pow(x8,7)*x9-47*x1*pow(x10,3)*pow(x3,4)*x4*pow(x6,3)*pow(x7,4)*x8*pow(x9,2)-72*x1*x3*pow(x7,4)*pow(x8,11)*pow(x9,2)+16*x1*pow(x10,2)*pow(x3,3)*pow(x4,4)*pow(x5,2)*pow(x6,4)*pow(x8,2)-84*x1*pow(x2,4)*pow(x3,6)*x4*pow(x5,4)*pow(x7,2)-45*pow(x1,3)*x10*pow(x2,3)*x4*pow(x5,2)*x6*pow(x7,4)*pow(x9,2)-34*x10*x2*x4*x5*pow(x6,2)*pow(x7,4)*pow(x8,4)*pow(x9,2),
    //     -69*pow(x1,4)*x2*pow(x3,8)*pow(x4,2)*pow(x6,2)*x7*x8*x9-63*pow(x10,3)*pow(x2,5)*pow(x3,4)*pow(x4,3)*pow(x7,2)*pow(x9,3)-48*x10*pow(x3,4)*pow(x4,7)*x5*pow(x7,2)*x8*pow(x9,4)+2*pow(x1,3)*pow(x10,8)*pow(x3,3)*pow(x4,2)*pow(x5,2)*x7+53*pow(x2,4)*x6*pow(x7,12)*pow(x8,2)+30*pow(x1,5)*x2*x3*pow(x4,3)*x5*pow(x6,2)*pow(x7,2)*x8*pow(x9,2)+70*pow(x3,5)*pow(x4,4)*x5*pow(x6,2)*pow(x8,2)*pow(x9,4)-93*pow(x1,5)*pow(x3,2)*pow(x5,3)*x6*x7*pow(x8,4)*x9-62*pow(x1,3)*x10*x2*pow(x3,2)*pow(x4,6)*pow(x5,3)*x9-55*x1*pow(x6,3)*x7*pow(x9,7)};
    //     for (int i=0;i<10;i++)
    //     {
    //         auto index=cnf.get_polyz(poly[i]);
    //         cnf.cnf().push_back(std::vector<std::pair<size_t,char>>());
    //         cnf.cnf().back().push_back({index,'<'});
    //     }
        

    // }
   
}