#include "smtlib.hh"
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
std::string get_cmd_option(std::vector<std::string>& arg,const std::string & option)
{
    auto p=std::find(arg.begin(),arg.end(),option);
    if (p!=arg.end() && (++p)!=arg.end())
    {
        return *p;
    }
    return "";
}
void to_maple(const std::string& file_name, bool is_rename,std::ostream & o)
{
    auto t1=clock();
    auto lib=smt::smtlib::read_smtlib2(file_name,is_rename);
    // std::cout<<lib<<std::endl;
    std::cout<<"libtime="<<double(clock()-t1)/CLOCKS_PER_SEC<<"s\n"; 
    auto t2=clock();
    auto cnf=smt::NRA::smtlib_to_cnf(lib);
    std::cout<<"cnftime="<<double(clock()-t2)/CLOCKS_PER_SEC<<"s\n"; 
    o<<"Eample:=";
    cnf.to_maple(o,file_name);
    o<<":";
    // std::map<clpoly::variable,double> mv;
    // for (auto &i:cnf.vars())
    //     mv[i]=0;
    // auto t3=clock();
    // cnf.assign(mv);
    // std::cout<<"assign="<<double(clock()-t3)/CLOCKS_PER_SEC<<"s\n"; 
    
}
int main(int argc, char const *argv[])
{
    std::vector<std::string> arg=init_cmd_option(argc,argv);
    std::string file_name=get_cmd_option(arg,"-f");
    bool is_rename=cmd_option_exists(arg,"--var_rename");
    bool is_no_unsimple_eq=cmd_option_exists(arg,"--no_unsimple_eq");
    bool is_no_unsat=cmd_option_exists(arg,"--no_unsat");
    if (cmd_option_exists(arg,"--help")){
        std::cout<<"-f"<<std::endl;
        std::cout<<"-d"<<std::endl;
        std::cout<<"-o"<<std::endl;
        std::cout<<"--var_rename"<<std::endl;
        std::cout<<"--no_unsimple_eq"<<std::endl;
        std::cout<<"--no_unsat"<<std::endl;
        return 0;
    }
    std::cout<<"var_rename="<<is_rename<<" no_unsimple_eq="<<is_no_unsimple_eq<<" is_no_unsat="<<is_no_unsat<<std::endl;
    if (!file_name.empty())
    {
        std::string file_out_name=get_cmd_option(arg,"-o");
        if (!file_out_name.empty())
        {
            std::filesystem::path p(file_out_name);
            if (!p.parent_path().empty())
                std::filesystem::create_directories(p.parent_path());
            std::ofstream o(p);
            if (!o.is_open()){
                throw std::invalid_argument("文件开启失败");
            }
            to_maple(file_name,is_rename,o);
            o.close();
        }
        else{
            to_maple(file_name,is_rename,std::cout);
        }
        // std::cout<<smt::ddd;
    }
    else{
        std::string file_dir=get_cmd_option(arg,"-d");
        if (!file_dir.empty())
        {
            std::filesystem::recursive_directory_iterator files(file_dir);
            std::string file_out_name=get_cmd_option(arg,"-o");
            if (!file_out_name.empty())
            {
                std::filesystem::create_directories(file_out_name);
            }
            else
            {
                file_out_name="__result";
            }
            std::filesystem::path op(file_out_name);
            std::filesystem::path fname_p=op/("name_list.mpl");
            std::filesystem::path fname_csv_p=op/("file_list.csv");
            
            if (!fname_p.parent_path().empty())
                std::filesystem::create_directories(fname_p.parent_path());
            std::ofstream fname(fname_p);
            std::ofstream fname_csv(fname_csv_p);
            
            if (!fname.is_open() || !fname_csv.is_open())
            {
                throw std::invalid_argument("文件保存失败");
            }       
            fname<<"namelist:=[";
            bool fname_b=true;
            size_t index=0;
            for (auto &it:files)
            {
                if (it.path().string().size()>=5 && it.path().string().substr(it.path().string().size()-5,it.path().string().size())==".smt2")
                {
                    auto t=clock();
                    std::filesystem::path fout_p=op/(std::filesystem::relative(it.path(),file_dir).string()+".mpl");
                    if (!fout_p.parent_path().empty())
                        std::filesystem::create_directories(fout_p.parent_path());
                    std::cout<<"file="<<it.path()<<":\n";
                    bool is_exist_unsimpleeq=false;
                    {
                        auto t1=clock();
                        try
                        {
                            auto lib=smt::smtlib::read_smtlib2(it.path().string(),is_rename);
                            std::cout<<"libtime="<<double(clock()-t1)/CLOCKS_PER_SEC<<"s "; 
                            if (is_no_unsat && lib.get_info(":status")=="unsat")
                            {
                                std::cout<<"skip"<<std::endl; 
                                fname_csv<<it.path()<<","<<2<<std::endl;
                                continue;;
                            }
                            auto t2=clock();
                            auto cnf=smt::NRA::smtlib_to_cnf(lib,is_no_unsimple_eq);
                            std::cout<<"cnftime="<<double(clock()-t2)/CLOCKS_PER_SEC<<"s "; 
                            
                            if (is_no_unsat && cnf.empty())
                            {
                                std::cout<<"skip"<<std::endl; 
                                fname_csv<<it.path()<<","<<3<<std::endl;
                                continue;
                            }
                            std::ofstream fout(fout_p);
                            if (!fout.is_open())
                            {
                                throw std::invalid_argument("文件保存失败:"+fout_p.string());
                            }
                            fout<<"Eample:=";
                            cnf.to_maple(fout,it.path().string());
                            is_exist_unsimpleeq=cnf.is_exist_unsimpleeq();
                            fout<<":";
                            fout.close();
                        }
                        catch(const std::exception& e)
                        {
                            std::cout << e.what() << '\n';
                            std::cerr << it.path()<<"read filed."<<e.what()<<"\n";
                            fname_csv<<it.path()<<","<<4<<std::endl;
                            continue;
                        } 
                    }
                    if (fname_b)
                        fname_b=false;
                    else
                        fname<<",\n";
                    fname<<"["<<fout_p<<","<<is_exist_unsimpleeq<<"]"<<std::endl;
                    fname_csv<<it.path()<<","<<is_exist_unsimpleeq<<std::endl;
                    ++index;
                    std::cout<<"index="<<index<<" ";
                    std::cout<<"out="<<fout_p<<" ";
                    std::cout<<"time="<<double(clock()-t)/CLOCKS_PER_SEC<<"s"<<std::endl; 
                }
            }
            fname<<"]:\n";
            fname.close();
            fname_csv.close();
        }else{
            throw std::invalid_argument("参数缺失 -f/d");
        }
    }
    
    // std::filesystem::recursive_directory_iterator files(file_name);
    // for (auto &it:files)
    // {
    //     std::cout<< it.path()<<std::endl;
    // }

    // auto lib=smt::smtlib::read_smtlib2(file_name,cmd_option_exists(arg,"--var_rename"));
    // // std::cout<<lib<<std::endl;
    // auto cnf=smt::NRA::smtlib_to_cnf(lib);
    // // std::cout<<cnf<<std::endl;
    // // std::cout<<std::endl;
    // // cnf.to_maple(std::cout,file_name);
    // std::string file_out_name=get_cmd_option(arg,"-o");
    // if (!file_out_name.empty())
    // {
    //     std::ofstream o(file_out_name);
    //     cnf.to_maple(o,file_name);
    // }
    // else{
    //     cnf.to_maple(std::cout,file_name);
    // }
    // // {
    // //     int index=0;
    // //     for (auto &i:cnf.polys())
    // //     {
    // //         std::cout<<(index++)<<":"<<std::endl;
    // //         std::cout<<i<<std::endl;
    // //         for(auto &j:i.variables())
    // //             std::cout<<"{"<<j.first<<","<<j.second<<"}, ";
    // //         std::cout<<std::endl; 
            
    // //     }
    // // }
    return 0;
}

