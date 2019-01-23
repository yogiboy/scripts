#!/usr/bin/perl
#
# Author: Navshobh Magotra
# Desc:   This script can be used to find largest files or directories in a filesystem.
#         It supports some nice features also. e.g. to generate a mail template that can be sent to application support for cleaning up files.
#         By default the script will show 10 largest files in the filesystem.
#
#         Please run with [-h] or --help to get more help.
#
# Note:   Not recommended to run on very busy Producion servers with very big filesystems as it can take lots of CPU for finding, sorting etc.
#
#
# 1.1 Wrote splicehash function and made some changes so that hash limit doesnt cross $MAX_LIMIT  and any point of time to check memory eating.This
#     can make the script slower but slow scipt is much worthy than a slow server. Also sets the priority of the script to lowest 19.
#
# 1.2 Made changes so that it works on relative paths also. Added [-j] option so that we are able to find files only just iniside the directory specified.
#

setpriority(0, 0, 19); #sets the priority of the script to lowest value 19 so that it does not interfere with processing on busy systems

use strict;
use File::Find;
use Getopt::Long;
use Data::Dumper;
use Cwd qw(abs_path);
#use warnings 'File::Find';

#
#Global Variables Declaration
#
my ($dirflag,$fsize,$just,$fileflag,$count,$tempflag,$newtime,$oldtime,$helpflag);
my (%fnlhash,@sortfnl);
my (%dirsizehash,%truefnlhash,%truedirhash);
my $MAX_LIMIT=100; # So that element count of hashes used never cross the set count. To check that hash doesnt get  unmanageable size and eat up memory.
my $subject;
#
#Help Section
#
sub usage
{
    print <<USAGE;
Usage: $0 [ -d | -f ] [-c] [-t] [-o <duration>] [-n <duration>] <<filesystem>>

             --directory [-d]   Print the largest directories inside the filesystem
             --file      [-f]   Print the largest files inside the filesystem
             --just      [-j]   Find files just in the directory specified. Do not descend directories. To be used with [-f] option.
             --size      [-s]   Specify filesize in bytes. Only search for files of size greater than specified size. Default value is 1MB.
             --count     [-c]   Specify count of number of largest files or directories to be printed. Default value is 10. Max value is $MAX_LIMIT.
             --template  [-t]   Generate and print a nice mail template that can be sent to support people for cleaning up files.
             --older     [-o]   Only take into account files or directories modified before specified duration i.e. older than
             --newer     [-n]   Only take into account files or directories modified since specified duration i.e. newer than

[-o] and [-n] options take arguements where we can specify time duration in months,days and hours.
e.g. 20m,20d and 20h would mean 20 months,20 days and 20 hours respectively.

Note: You cannot specify both [-d] and [-f] options at the same time.
Note: Only one filesystem name can be specified.
Note: The script will never traverse across different filesystems. It works exactly like -xdev option in find command.

e.g.

$0 -f /export/home                     (Display by default 10 largest files inside /export/home)
$0 -d /export/home                     (Display by default 10 largest directories inside /export/home)

$0 -f /export/home -j                  (Only find files just inside /export/home. Do not descend any directories)
$0 -f /export/home -c 50               (Display 50 largest files instead of default 10)
$0 -f /export/home -o 2m               (Only consider files where last modified time is before last 2 months)
$0 -f /export/home -n 2m               (Only consider files where last modified time is within last 2 months)
$0 -f /export/home -s 10000000         (Only consider files with size greater than 10 MB. Default is 1048576 bytes or 1MB)
USAGE
exit 1;
}

#
#Get Inputs and also Check for wrong inputs
#
sub getcheckinput
{
    my $options=GetOptions
    (
       "directory" => \$dirflag,
        "file" => \$fileflag,
        "just" => \$just,
        "size=i" => \$fsize,
        "count=i" => \$count,
        "template" => \$tempflag,
        "older=s" => \$oldtime,
        "newer=s" => \$newtime,
        "help" => \$helpflag
    );

    if (!$options or defined $helpflag  or scalar(@ARGV)!=1)
    {
        usage();
    }

    if (!(defined $fileflag xor defined $dirflag))
    {
        print "You have to specify one out of [-d] and [-f] options. And you cannot specify both of these. Exiting now !\n";
        usage();
    }
    if (defined $count and $count >=$MAX_LIMIT)
    {
        print "You have to specify count less than $MAX_LIMIT\n";
        usage();
    }
    $count ||= 10;
    $fsize ||= 1024*1024;
    if (defined $newtime)
    {
        if ($newtime =~ /^(\d+)m/)
        {
            $newtime=(scalar time()) - ($1*2592000);
        }
        elsif($newtime =~ /^(\d+)d/)
        {
            $newtime=(scalar time()) - ($1*86400);
        }
        elsif($newtime =~ /^(\d+)h/)
        {
            $newtime=(scalar time()) - ($1*3600);
        }
        else
        {
            print "Invalid [-n] option supplied. Continuing with default value of 0\n";
            $newtime=0;
        }
    }
    else
    {
        $newtime=0;
    }
    if (defined $oldtime)
    {
        if ($oldtime =~ /^(\d+)m/)
        {
            $oldtime=(scalar time()) - ($1*2592000);
        }
        elsif ($oldtime =~ /^(\d+)d/)
        {
            $oldtime=(scalar time()) - ($1*86400);
        }
        elsif ($oldtime =~ /^(\d+)h/)
        {
            $oldtime=(scalar time()) - ($1*3600);
        }
        else
        {
            print "Invalid [-o] option supplied. Continuing with default value of Current time\n";
            $oldtime=time()+3600;
        }
    }
    else
    {
        $oldtime =time()+10000; #Buffer time for script
    }

}

#
#Convert size from no. of bytes toi some human readable format.
#
sub convertsize
{
    my $size_bytes=shift;
    if ($size_bytes < 1024)
    {
        $size_bytes .= ' B';
        return $size_bytes;
    }
    elsif ( $size_bytes < 1024*1024 )
    {
        return (sprintf("%1.2f", ($size_bytes/1024)).' KB');
    }
    elsif ( $size_bytes < 1024*1024*1024)
    {
        return (sprintf("%1.2f", ($size_bytes/(1024*1024))).' MB');
    }
    else
    {
        return (sprintf("%1.2f", ($size_bytes/(1024*1024*1024))).' GB');
    }
}

#
#Sort the hash by size
#
sub sorthashkeys
{
    my $hashref=shift;
    #Sort the hash by generating an @sorted_keys array that contains the keys of hash (sorted by the size value)
    my @sorted_keys= sort { $hashref->{$b}->[0] <=> $hashref->{$a}->[0] } keys %$hashref;
    return (@sorted_keys);

}
#
#Print output
#

sub printoutput
{
    my $hashref=shift;
    my $sortref=shift;
    my ($groupname,$username);
    my $long=length((@$sortref)[0]);
    my $namelen=0;
    if ($subject =~ /^\./)
    {
      $subject=abs_path $subject;
      print ("NOTE: All below files/directories are under $subject\n");
    }
    foreach (@$sortref)
    {
        if ((getpwuid $hashref->{$_}->[2])[0] =~ /^a\d{6}/)
        {
          my $realname=(getpwuid $hashref->{$_}->[2])[6];
          ($namelen < length $realname) && ($namelen=length $realname);
        }
        (length($_) > $long) && ($long=length($_));
    }
    $namelen=$namelen+11;
    print "=" foreach (1 .. ${long}+${namelen}+51); print "\n";
    printf ("%-${long}s  %-13s %-${namelen}s %-9s %-15s\n", "Name", "Size", "User","Group","Last Modified");
    print "=" foreach (1 .. ${long}+$namelen+51); print "\n";
    foreach (@$sortref)
    {
        if ((getgrgid $hashref->{$_}->[3])[0] eq "")
        {
            $groupname=$hashref->{$_}->[3];
        }
        else
        {
            $groupname=(getgrgid $hashref->{$_}->[3])[0];
        }
        if ((getpwuid $hashref->{$_}->[2])[0] eq "")
        {
            $username=$hashref->{$_}->[2];
        }
        else
        {
            $username=(getpwuid $hashref->{$_}->[2])[0];
            if ($username =~ /^a\d{6}/)
            {
                my $realname=(getpwuid $hashref->{$_}->[2])[6] if ($username =~ /^a\d{6}/);
                $username="$username ($realname)";
            }
        }
        printf ("%-${long}s  %-13s %-${namelen}s %-9s %-10s\n", $_, convertsize ($hashref->{$_}->[0] ),$username, $groupname, my $time=localtime $hashref->{$_}->[1]);
    }
}
#
# Splice a hash????. Ahh, It will take two hashes and then combine them and sort the hash keys of resulting hash and then trim off that hash so that
# it contains the no. of elements that are equal to the first hash passed. This is just to keep in count the hash elements so that a hash doesnt grow to
# unmanageable size.
#
sub splicehash
{
    my $hashref1=shift;
    my $hashref2=shift;
    foreach (keys %$hashref2)
    {
        $hashref1->{$_}=$hashref2->{$_};
    }
    my @sort1=sorthashkeys($hashref1);
    splice @sort1,$count;
    my %temp;
    foreach (@sort1)
    {
       $temp{$_}=$hashref1->{$_};
    }
    %$hashref1=%temp;
    %$hashref2=(); # Nullify the second hash passed
    return;
}
#
# Trim the directory hash so that it doesnt exceed the $MAX_LIMIT.
#
sub splicedirhash
{
    my $hashref1=shift;
    my $hashref2=shift;
    foreach (keys %$hashref2)
    {
       $hashref1->{$_}=$hashref2->{$_};
    }
    my @sort1=sort { $hashref1->{$b} <=> $hashref1->{$a} } keys %$hashref1;
    splice @sort1,$count;
    my %temp;
    foreach (@sort1)
    {
        $temp{$_}=$hashref1->{$_};
    }
    %$hashref1=%temp;
    %$hashref2=();
    return;
}
#
#Main Program
#
getcheckinput();
$subject=shift;
die "$subject: No Such Direcory Exists.\n" if (! -d $subject);
if ( defined $fileflag) #if biggest files are required
{

    find(
        {
            preprocess => \&condition,
            wanted => \&dothisfile
        },  $subject);

    sub condition
    {
        return  @_ if ! defined $just;
        return grep {-f} @_;
    }
    sub dothisfile
    {
        my ($dev,$ino,$mode,$nlink,$uid,$gid,$rdev,$size,$atime,$mtime,$ctime,$blksize,$blocks) = lstat($_);
        return if $File::Find::prune=($dev != $File::Find::topdev) or ($size < $fsize);
        #Generate a hash of arrays with filename being the key and attributes the values
        $fnlhash{$File::Find::name} = [$size,$mtime,$uid,$gid] if (-f  and $mtime>$newtime and $mtime<$oldtime);
        if ((scalar keys %fnlhash) == $MAX_LIMIT) #Nice logic to check that hash doesnt cross $MAX_LIMIT
        {
             splicehash(\%truefnlhash,\%fnlhash);
        }
    }
}
elsif (defined $dirflag) #if biggest directories are required
{
    find(
        {
            wanted => \&dothisdir
        },  $subject);
    sub dothisdir
    {
        my ($dev,$ino,$mode,$nlink,$uid,$gid,$rdev,$size,$atime,$mtime,$ctime,$blksize,$blocks) = lstat($_);
        return if $File::Find::prune=($dev != $File::Find::topdev);
        #Generate a hash of directories with directory names as keys and their sizes as values
        $dirsizehash{$File::Find::dir}+=$size if -f ;
        if ((scalar keys %dirsizehash) == $MAX_LIMIT )
        {
            splicedirhash(\%truedirhash,\%dirsizehash);
        }
    }
    splicedirhash(\%truedirhash,\%dirsizehash);
    foreach (keys %truedirhash)
    {
        my ($dev,$ino,$mode,$nlink,$uid,$gid,$rdev,$size,$atime,$mtime,$ctime,$blksize,$blocks) = lstat($_);
        #Generate a hash of arrays with directory name being the key and attributes the values
        $fnlhash{$_}=[$truedirhash{$_},$mtime,$uid,$gid] if ($truedirhash{$_} > $fsize and $mtime>$newtime and $mtime<$oldtime);
    }
}
else
{
    print "Something Unexpected occured. Exiting now !!\n";
    usage();
}
splicehash(\%truefnlhash,\%fnlhash);
@sortfnl=sorthashkeys(\%truefnlhash);
splice @sortfnl,$count;
if (defined $tempflag)
{
    #Generate a nice template e-mail to be sent to supoort people.
    my $hostname=`hostname`;
    chomp $hostname;
    my $subject_r=$subject;
    $subject_r=abs_path $subject if ($subject =~ /^\./);
    print <<MAIL;
#########
Subject:-
#########

Filesystem usage for $subject_r exceeds threshold on $hostname

######
Body:-
######

Hi Guys,

     We have this alert on high filesystem usage for "$subject_r" on server "$hostname". Upon investigation its found that below files/directories are taking up most of the space. Can you please try to clean up some of these files/directories so that the usage can get below threshold and any kind of space issue be avoided.


MAIL
    printoutput(\%truefnlhash,\@sortfnl);
    print <<MAIL;


Please be aware, that full filesystems can/will

- Continue to generate alerts
- Stop an application from functioning.
- Stop a server from functioning and lead to service outage.
MAIL
    print ("\n");
}
else
{
    printoutput(\%truefnlhash,\@sortfnl);
}
exit 0;
