#include "smtlib.hh"
#include "nra_analyze.hh"
#include <algorithm>
#include <filesystem>
#include <time.h>
#include <map>
#include "argparse.hh"
#include <iostream>

double get_smt_chord(const std::string& file_name)
{
    auto t1=clock();
    auto lib=smt::smtlib::read_smtlib2(file_name);
    // std::cout<<lib<<std::endl;
    std::cout<<"libtime="<<double(clock()-t1)/CLOCKS_PER_SEC<<"s\n"; 
    auto t2=clock();
    auto cnf=smt::NRA::smtlib_to_cnf(lib);
    std::cout<<"cnftime="<<double(clock()-t2)/CLOCKS_PER_SEC<<"s\n"; 
    auto g=cnf.to_associatedgraph();
    double ans=clpoly::graph_diff_score(clpoly::chordal_completion(g),g);
    std::cout<<"chordal: "<<ans<<std::endl;
    std::cout<<"sparse: "<<clpoly::graph_diff_score(connected_branch_graph(g),g)<<std::endl; 
    // std::cout<<"chord: "<<ans<<std::endl;
    return ans;
}

int main(int argc, char const *argv[])
{
    auto myparse=argparse::argparse("chordofsmt");
    myparse.add_arg("smtfile","smtlib2 file","");
    myparse.add_arg("smtfiledir","smtlib2 file dir","");
    std::string parse_error_msg;
    if (!myparse.parse(argc,argv,parse_error_msg))
    {
        std::cout<<parse_error_msg<<std::endl;
        exit(1);
    }
    if (myparse.has("help"))
    {
        std::cout<<myparse.help()<<std::endl;
        exit(1);
    }
    auto smtfile=myparse.get("smtfile");
    if (!smtfile.empty())
    {
        try
        {
            get_smt_chord(smtfile);
        }
        catch(const std::exception& e)
        {
            std::cerr << e.what() << '\n';
            exit(1);
        }
    }
    auto smtdir=myparse.get("smtfiledir");
    if (!smtdir.empty())
    {
        std::vector<std::string> smtfiles;
        for (const auto & entry : std::filesystem::recursive_directory_iterator(smtdir))
        {
            if (entry.path().extension()==".smt2")
            {
                smtfiles.push_back(entry.path());
            }
        }
        std::sort(smtfiles.begin(),smtfiles.end());
        for (auto& smtfile:smtfiles)
        {
            std::cout<<smtfile<<std::endl;
            try
            {
                get_smt_chord(smtfile);
            }
            catch(const std::exception& e)
            {
                std::cerr << e.what() << '\n';
                
            }
        }
    }
}