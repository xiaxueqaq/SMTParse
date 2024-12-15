#ifndef __ARGPARSE_HH__
#define __ARGPARSE_HH__
#include <vector>
#include <set>
#include <map>
#include <string>
#include <iostream>
namespace argparse{
    class argparse
    {
        private:
            std::string __program_name;
            std::string __program_description;
            std::set<std::string> __args;
            std::set<std::string> __required_args;
            std::map<std::string,std::string> __args_description;
            std::map<std::string,std::string> __args_short;
            std::map<std::string,std::string> __option;
        public:
            inline argparse()
            {
                add_arg("help","print help message","h");
            }
            inline argparse(const std::string & program_name,const std::string & program_description="")
            {
                __program_name=program_name;
                __program_description=program_description;
                add_arg("help","print help message","h");
            }
            inline bool add_arg(const std::string & arg,const std::string & description="",const std::string & short_arg="", bool is_required=false, const std::string & default_value="")
            {
                if (arg.empty())
                    return false;
                if (__args.find(arg)!=__args.end())
                    return false;
                __args.insert(arg);
                __args_description[arg]=description;
                if (short_arg!="")
                    __args_short[short_arg]=arg;
                if (is_required)
                    __required_args.insert(arg);
                if (default_value!="")
                    __option[arg]=default_value;
                return true;
            }
            
            inline std::string help() const
            {
                std::string ret;
                ret+="Usage: "+__program_name+" [options]\n";
                ret+=__program_description+"\n";
                ret+="Options:\n";
                for (auto& arg:__args)
                {
                    ret+="  --"+arg;
                    auto p=__args_short.find(arg);
                    if (p!=__args_short.end())
                    {
                        ret+=",-"+p->second;
                    }
                    ret+="\n";
                    if (!__args_description.at(arg).empty())
                        ret+="    "+__args_description.at(arg)+"\n";
                    if (__option.find(arg)!=__option.end())
                    {
                        ret+="    default: "+__option.at(arg)+"\n";
                    }
                    if (__required_args.find(arg)!=__required_args.end())
                    {
                        ret+="    required\n";
                    }

                }
                return ret;
            }
            inline void print_help() const
            {
                std::cout<<"Usage: "<<__program_name<<" [options]"<<std::endl;
                std::cout<<__program_description<<std::endl;
                std::cout<<"Options:"<<std::endl;
                for (auto& arg:__args)
                {
                    std::cout<<"  --"<<arg;
                    auto p=__args_short.find(arg);
                    if (p!=__args_short.end())
                    {
                        std::cout<<",-"<<p->second;
                    }
                    std::cout<<std::endl;
                    std::cout<<"    "<<__args_description.at(arg)<<std::endl;
                }
            }

            inline bool parse(int argc, char const *argv[], std::string & error_msg)
            {
                for (int i=1;i<argc;++i)
                {
                    std::string arg=argv[i];
                    if (arg[0]=='-')
                    {
                        if (arg[1]=='-')
                        {
                            auto p=__args.find(arg.substr(2));
                            if (p!=__args.end())
                            {
                                if (i+1<argc)
                                {
                                    __option[arg.substr(2)]=argv[i+1];
                                    ++i;
                                }
                                else
                                {
                                    __option[arg.substr(2)]="";
                                }
                            }
                            else
                            {
                                error_msg="invalid option "+arg;
                                return false;
                            }
                        }
                        else
                        {
                            auto p=__args_short.find(arg.substr(1));
                            if (p!=__args_short.end())
                            {
                                if (i+1<argc)
                                {
                                    __option[p->second]=argv[i+1];
                                    ++i;
                                }
                                else
                                {
                                    __option[p->second]="";
                                }
                            }
                            else
                            {
                                error_msg="invalid option "+arg;
                                return false;
                            }
                        }
                    }
                    else
                    {
                        error_msg="invalid option "+arg;
                        return false;
                    }

                }
                for (auto& arg:__required_args)
                {
                    if (__option.find(arg)==__option.end())
                    {
                        error_msg="required option "+arg+" is missing";
                        return false;
                    }
                }
                return true;
            }
            inline bool parse(int argc, char const *argv[])
            {
                std::string error_msg;
                return parse(argc,argv,error_msg);
            }
            inline bool has(const std::string & option) const
            {
                return __option.find(option)!=__option.end();
            }
            inline const std::string & get(const std::string & option) const
            {
                static const std::string empty_string="";
                auto p=__option.find(option);
                if (p!=__option.end())
                    return p->second;
                return empty_string;
            }
            ~argparse()
            {

            }
    };
}
#endif