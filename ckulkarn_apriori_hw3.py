#!/usr/bin/python
#		
#
#	Chinmay Kulkarni (netid: ckulkarn)
#
# Code to implement the Apriori Algorithm. The topic files and vocabulary mapping is used as an input.
# Output is patterns generated in the "patterns/" directory.
# 
# Execution:
#	python ckulkarn_apriori_hw3.py <min_support_value> 
#
# If no min_support value is passed as a command line argument then the default value of 0.01 is used.
#
from itertools import combinations
import sys
import os
import math

#Global Variables
min_support = 0.01																											#Minimum Support value for deciding the frequent patterns.
#File locations:
location = "./data-assign3/"
vocab = location + "vocab.txt"
patterns_location = "./patterns/"
max_patterns_location = "./max/"
closed_patterns_location = "./closed/"
pure_patterns_location = "./purity/"
phraseness_patterns_location = "./phraseness/"
completeness_patterns_location = "./completeness/"
#Mapping provided by the vocab.txt file
mapping = {}
#Dictionary of Frequent item lists for all levels (per topic file). Thus, the key corresponds to the topic and the value is a list of frequent item lists.
#Each member of the list except for the first member is a dictionary of tuple:frequency pairs where each tuple is a pattern.
frequent_item_lists_for_topic = {}
topic_files = [location + 'topic-0.txt', location + 'topic-1.txt', location + 'topic-2.txt', location + 'topic-3.txt', location + 'topic-4.txt']


#This function stores the mapping provided in the vocab.txt file into
#a dictionary (hashmap).
def vocab_map(file_name):
	print "Mapping the term indices to the words as per " + file_name + "\n"
	fd = open(file_name,'r')
	lines = fd.readlines()
	for line in lines:
		line = line.split('\t')
		mapping[int(line[0])] = line[1].strip()
	fd.close()


#This function is used to fill the D_matrix that we will use for calculating purty.
def make_D_matrix_for_purity():
	D = {(0,0):10047,(0,1):17326,(0,2):17988,(0,3):17999,(0,4):17820,
	(1,0):17326,(1,1):9674,(1,2):17446,(1,3):17902,(1,4):17486,
	(2,0):17988,(2,1):17446,(2,2):9959,(2,3):18077,(2,4):17492,
	(3,0):17999,(3,1):17902,(3,2):18077,(3,3):10161,(3,4):17912,
	(4,0):17820,(4,1):17486,(4,2):17492,(4,3):17912,(4,4):9845}	
	return D


#This function is used to find the frequency of candidates of a tuple in the transactions.
def find_frequency_of_candidates_in_transactions(transactions,cand_tuple):
	tuple_freq = 0
	for transaction in transactions:
		items_transaction = transaction.split()
		flag = 0
		for candidate in cand_tuple:
			if candidate not in items_transaction:
				flag = 1
				break
		if flag == 0:
			tuple_freq += 1
	return tuple_freq
			

#This function is used to generate the initial (Level 1) candidate set.
def generate_initial_candidate_items(topic_file,transactions):
	print "Generating the Initial Candidate Itemset"
	candidate_list = {}
	all_terms = topic_file.read().split()
	all_terms = set(all_terms)
	for term in all_terms:
		candidate_list[(term,)] = find_frequency_of_candidates_in_transactions(transactions,(term,))
	return candidate_list
		

#This is the generic function which is used to generate the candidate itemset at every level.
def generate_candidate_items(transactions,freq_itemset_k,prev_level):
	print "Generating Candidate Itemset from Frequent Itemset of level " + str(prev_level)
	candidate_list = {}																										#We are storing the itemsets as a dictionary as <(tuple of items),frequency> pairs.
	members = freq_itemset_k.keys()
	for member in members:																								#Iterate over the list of tuples (keys).
		for next_member in members[members.index(member) + 1:]:
			flag = 0
			union_items = tuple(set(member) | set(next_member))
			if len(union_items) == prev_level + 1:														#We can only combine the sets if the union contains prev_level + 1 elements.
				for subset in combinations(union_items,prev_level):							#Iterate over every subset of the union of items and check whether every "prev_level" sized 
					if subset not in members:																			#subset of the new candidate items that we want to add are in the frequent itemset.
						flag = 1
						break
				if (flag == 0):																									#Only add the items to the frequent itemset if all the item's subsets are there in the previous 
					if union_items not in candidate_list:													#level's frequent itemset.
						candidate_list[union_items] = find_frequency_of_candidates_in_transactions(transactions,union_items)
	return candidate_list


#This function is used to record the frequent itemsets found in a file.
def record_freq_pattern(frequent_itemset,total_transactions,pattern_file):
	if (len(frequent_itemset) != 0):
		print "Recording the Frequent Patterns to the file"
	for tuple_pattern in frequent_itemset:
		word_pattern = ''
		for member in tuple_pattern:
			word_pattern += mapping[int(member)] + ' '												#Store the mapping of each member of the tuple of the list of tuples in the frequent itemset. 
		pattern_file.write('['+ str(float(frequent_itemset[tuple_pattern])/float(total_transactions)) + '] [' + word_pattern + ']\n') 


#This function is the generic function used to generate frequent itemsets by checking which items
#out of the candidate itemset satisfy the minimum support.
def generate_freq_items(candidates,total_transactions,pattern_file,k):
	print "Generating the Frequent Itemset for level " + str(k)
	frequent_itemset = {}
	for item in candidates:
		if (float(candidates[item])/float(total_transactions) >= min_support):
			frequent_itemset[item] = candidates[item]
	record_freq_pattern(frequent_itemset,total_transactions,pattern_file)
	return frequent_itemset
	
		
#This function is used to sort the [metric] [items...] values in the file by the metric values in that file.
def sort_by_metric(pattern_file,metric):
	print "Sorting the files by the " + metric + " value of frequent items"
	metric_recorded_patterns = pattern_file.readlines()
	pattern_file.seek(0)
	metric_values = []
	for line in metric_recorded_patterns:
		line = line.split()
		metric_values.append(float(line[0].split('[')[1].split(']')[0]))
	metric_values.sort(reverse=True)
	for value in metric_values:
		for line in  metric_recorded_patterns:
			if value == float(line.split()[0].split('[')[1].split(']')[0]):
				pattern_file.write(line) 
				metric_recorded_patterns.remove(line)
				break

	
#This function implements the apriori algorithm
def apriori(topic):
	print "Running Apriori Algorithm for the topic file\t" + topic
	list_of_freq_itemsets = [0]
	topic_file = open(topic,'r')
	pattern_file = open(patterns_location + 'pattern-' + str(topic_files.index(topic)) + '.txt','w')
	transactions = topic_file.readlines()
	topic_file.seek(0)
	total_transactions = len(transactions)
	topic_file.seek(0)

	#We store the itemsets with their frequencies as a dictionary of <tuple,frequency> pairs.
	candidates = generate_initial_candidate_items(topic_file,transactions)
	freq_items = generate_freq_items(candidates,total_transactions,pattern_file,1)
	list_of_freq_itemsets.append(freq_items)
	frequent_item_lists_for_topic[topic] = list_of_freq_itemsets					#Store the first list of frequent items for 'topic'
	topic_file.close()
	k = 1
	while(len(freq_items) != 0):																					#Loop only until the frequent itemset generated is not empty.
		candidates = generate_candidate_items(transactions,freq_items,k)
		freq_items = generate_freq_items(candidates,total_transactions,pattern_file,k+1)
		list_of_freq_itemsets = frequent_item_lists_for_topic[topic]
		list_of_freq_itemsets.append(freq_items)
		frequent_item_lists_for_topic[topic] = list_of_freq_itemsets
		k += 1
	pattern_file.close()
	pattern_file = open(patterns_location + 'pattern-' + str(topic_files.index(topic)) + '.txt','r+')
	sort_by_metric(pattern_file,"support")
	pattern_file.close()


#This function is used to record the found max patterns to a file.
def record_max_pattern(pattern,support,total_transactions,max_pattern_file):
	word_pattern = ''
	for term in pattern:
		word_pattern += mapping[int(term)] + ' '														#Store the mapping of each member of the tuple of the list of tuples in the frequent itemset. 
	max_pattern_file.write('['+ str(float(support)/float(total_transactions)) + '] [' + word_pattern + ']\n') 


#This function is used to record the found closed patterns to a file.
def record_closed_pattern(pattern,support,total_transactions,closed_pattern_file):
	word_pattern = ''
	for term in pattern:
		word_pattern += mapping[int(term)] + ' '														#Store the mapping of each member of the tuple of the list of tuples in the frequent itemset. 
	closed_pattern_file.write('['+ str(float(support)/float(total_transactions)) + '] [' + word_pattern + ']\n') 
	

#This function is used to find the max patterns for a given topic.
def find_max_patterns(topic):
	print "Finding the Max Patterns for topic:\t" + topic
	topic_file = open(topic,'r')
	transactions = topic_file.readlines()
	total_transactions = len(transactions)
	topic_file.close()
	max_pattern_file = open(max_patterns_location + 'max-' + str(topic_files.index(topic)) + '.txt','w')

	list_of_freq_itemsets = frequent_item_lists_for_topic[topic]
	for l_k in list_of_freq_itemsets[1:]:
		l_k_keys = l_k.keys()
		if len(l_k) == 0:
			break
		higher_l_k = list_of_freq_itemsets[list_of_freq_itemsets.index(l_k) + 1]
		higher_l_k_keys = higher_l_k.keys()
		if len(higher_l_k) == 0:
			for pattern in l_k_keys:
				record_max_pattern(pattern,l_k[pattern],total_transactions,max_pattern_file)
			break
		for pattern in l_k_keys:
			for higher_pattern in higher_l_k_keys:
				flag = 0
				for term in pattern:
					if term in higher_pattern:	
						flag += 1
				if flag == len(pattern):																					#Found a superset.
					break
			if flag != len(pattern):
				record_max_pattern(pattern,l_k[pattern],total_transactions,max_pattern_file)

	print "Recorded the Max Patterns to the file"
	max_pattern_file.close()
	max_pattern_file = open(max_patterns_location + 'max-' + str(topic_files.index(topic)) + '.txt','r+')
	sort_by_metric(max_pattern_file,"support")
			

#This function is used to find closed patterns.
def find_closed_patterns(topic):
	print "Finding the Closed Patterns for topic:\t" + topic
	topic_file = open(topic,'r')
	transactions = topic_file.readlines()
	total_transactions = len(transactions)
	topic_file.close()
	closed_pattern_file = open(closed_patterns_location + 'closed-' + str(topic_files.index(topic)) + '.txt','w')
	
	list_of_freq_itemsets = frequent_item_lists_for_topic[topic]
	for l_k in list_of_freq_itemsets[1:]:
		if len(l_k) == 0:
			break
		higher_l_k = list_of_freq_itemsets[list_of_freq_itemsets.index(l_k) + 1]
		if len(higher_l_k) == 0:
			for pattern in l_k:
				record_closed_pattern(pattern,l_k[pattern],total_transactions,closed_pattern_file)
			break
		l_k_keys = l_k.keys()
		higher_l_k_keys = higher_l_k.keys()
		for pattern in l_k_keys:
			closed = 1
			for higher_pattern in higher_l_k_keys:
				flag = 0
				for term in pattern:
					if term in higher_pattern:	
						flag += 1
				if flag == len(pattern):
					if l_k[pattern] == higher_l_k[higher_pattern]:								#If the supports are the same, 'pattern' cannot be closed.	
						closed = 0
						break
			if closed == 1:		
				record_closed_pattern(pattern,l_k[pattern],total_transactions,closed_pattern_file)

	print "Recorded the Closed Patterns to the file"
	closed_pattern_file.close()
	closed_pattern_file = open(closed_patterns_location + 'closed-' + str(topic_files.index(topic)) + '.txt','r+')
	sort_by_metric(closed_pattern_file,"support")


#This function is used to find the second term (max term) in the formula for purity of a pattern.
def find_max_in_purity(pattern,topic,f_t_p):
	max_val = -1	
	other_topics = topic_files[:topic_files.index(topic)] + topic_files[topic_files.index(topic) + 1:]
	for other in other_topics:
		f_t1_p = 0
		list_of_freq_itemsets = frequent_item_lists_for_topic[other]
		for frequent_itemset_support in list_of_freq_itemsets[1:]:
			if pattern in frequent_itemset_support:
				f_t1_p = frequent_itemset_support[pattern]
		value_to_check = float(f_t_p + f_t1_p)/float(D[(topic_files.index(topic),topic_files.index(other))])
		if value_to_check > max_val:
			max_val = value_to_check
	return max_val


#This function is used to record the purity of patterns to a file.		
def record_pure_pattern(purity_value_of_pattern,pattern,pure_file):
	word_pattern = ''
	for term in pattern:
		word_pattern += mapping[int(term)] + ' '														#Store the mapping of each member of the tuple of the list of tuples in the frequent itemset. 
	pure_file.write('['+ str(purity_value_of_pattern) + '] [' + word_pattern + ']\n') 


#This function is used to sort items in the file by the support and purity values.
def sort_by_support_purity(pure_file,frequent_itemset_dicts,purity_pattern_list,total_transactions):
	print "Sorting the files by the (relative support)*(purity) value of frequent items"
	metric_pattern = {}
	for pattern in purity_pattern_list:
		purity = purity_pattern_list[pattern]
		for frequent_itemset_support in frequent_itemset_dicts:
			if pattern in frequent_itemset_support:
				relative_support = float(frequent_itemset_support[pattern])/float(total_transactions)
				break
		metric = float(purity) * float(relative_support)
		metric_pattern[pattern] = metric

	word_list = []
	for pattern in metric_pattern:
		word_pattern = ''
		for term in pattern:
			word_pattern += mapping[int(term)] + ' '
		words = '[' + str(metric_pattern[pattern]) + '] [' + word_pattern + ']\n'
		word_list.append(words)

	sort_by_support_purity = []
	for line in word_list:
		line = line.split()
		sort_by_support_purity.append(float(line[0].split('[')[1].split(']')[0]))
	sort_by_support_purity.sort(reverse=True)
	for new_metric in sort_by_support_purity:
		for line in word_list:
			if new_metric == float(line.split()[0].split('[')[1].split(']')[0]):
				pure_file.write(line)
				word_list.remove(line)
				break


#This function is used to find the purity of patterns.
def find_purity(topic,D_matrix):
	print "Finding the Purity for topic:\t" + topic
	pure_file = open(pure_patterns_location + 'purity-' + str(topic_files.index(topic)) + '.txt','w')
	purity_pattern = {}
	
	D_t = D[(topic_files.index(topic),topic_files.index(topic))]
	list_of_freq_itemsets = frequent_item_lists_for_topic[topic]
	for frequent_itemset_support in list_of_freq_itemsets[1:]:
		for pattern in frequent_itemset_support:
			f_t_p = frequent_itemset_support[pattern]
			term1 = math.log(float(f_t_p)/float(D_t))
			term2 = find_max_in_purity(pattern,topic,f_t_p)
			purity_value_of_pattern = float(term1) - float(math.log(float(term2)))
			purity_pattern[pattern] = purity_value_of_pattern
			record_pure_pattern(purity_value_of_pattern,pattern,pure_file)

	print "Recorded the Purity of Patterns to the file"
	pure_file.close()
	pure_file = open(pure_patterns_location + 'purity-' + str(topic_files.index(topic)) + '.txt','w')
	sort_by_support_purity(pure_file,list_of_freq_itemsets[1:],purity_pattern,D_t)
	pure_file.close()


#This function is used to record the phraseness of patterns to a file.
def record_phraseness_pattern(phraseness_value_of_pattern,pattern,phraseness_file):
	word_pattern = ''
	for term in pattern:
		word_pattern += mapping[int(term)] + ' '														#Store the mapping of each member of the tuple of the list of tuples in the frequent itemset. 
	phraseness_file.write('['+ str(phraseness_value_of_pattern) + '] [' + word_pattern + ']\n') 


#This function is used to find the phraseness of patterns.
def find_phraseness(topic,D_matrix):
	print "BONUS QUESTION: Finding the Phraseness for topic:\t" + topic
	phraseness_file = open(phraseness_patterns_location + 'phraseness-' + str(topic_files.index(topic)) + '.txt','w')
	
	D_t = D[(topic_files.index(topic),topic_files.index(topic))]
	list_of_freq_itemsets = frequent_item_lists_for_topic[topic]
	for frequent_itemset_support in list_of_freq_itemsets[1:]:
		for pattern in frequent_itemset_support:
			summation_f_t_w = 0.0
			f_t_p = frequent_itemset_support[pattern]
			term1 = math.log(float(f_t_p)/float(D_t))
			for word in pattern:
				summation_f_t_w += float(math.log(float(list_of_freq_itemsets[1][(word,)])/float(D_t)))
			phraseness_value_of_pattern = float(term1) - float(summation_f_t_w)
			record_phraseness_pattern(phraseness_value_of_pattern,pattern,phraseness_file)

	print "Recorded the Phraseness of Patterns to the file"
	phraseness_file.close()
	phraseness_file = open(phraseness_patterns_location + 'phraseness-' + str(topic_files.index(topic)) + '.txt','r+')
	sort_by_metric(phraseness_file,"phraseness")
	phraseness_file.close()


#This function is used to record the completeness of patterns to a file.
def record_completeness_pattern(completeness_value_of_pattern,pattern,completeness_file):
	word_pattern = ''
	for term in pattern:
		word_pattern += mapping[int(term)] + ' '														#Store the mapping of each member of the tuple of the list of tuples in the frequent itemset. 
	completeness_file.write('['+ str(completeness_value_of_pattern) + '] [' + word_pattern + ']\n') 


#This function is used to find the completeness of patterns.
def find_completeness(topic):
	print "BONUS QUESTION: Finding the Completeness for topic:\t" + topic
	completeness_file = open(completeness_patterns_location + 'completeness-' + str(topic_files.index(topic)) + '.txt','w')
	
	list_of_freq_itemsets = frequent_item_lists_for_topic[topic]
	for frequent_itemset_support in list_of_freq_itemsets[1:]:
		freq_itemset_dict_index = list_of_freq_itemsets.index(frequent_itemset_support)
		if freq_itemset_dict_index == len(list_of_freq_itemsets) - 1:
			break
		for pattern in frequent_itemset_support:
			max_freq_superset_pattern = 0
			f_t_p = frequent_itemset_support[pattern]
			superset_dict = list_of_freq_itemsets[freq_itemset_dict_index + 1]
			for superset_pattern in superset_dict:
				for term in pattern:	
					flag = 0
					if term not in superset_pattern:
						flag = 1
						break
				if flag == 0:
					if list_of_freq_itemsets[freq_itemset_dict_index + 1][superset_pattern] > max_freq_superset_pattern:
						max_freq_superset_pattern = list_of_freq_itemsets[freq_itemset_dict_index + 1][superset_pattern]
			completeness_value_of_pattern = 1 - float(max_freq_superset_pattern)/float(f_t_p)
			record_completeness_pattern(completeness_value_of_pattern,pattern,completeness_file)

	print "Recorded the Completeness of Patterns to the file"
	completeness_file.close()
	completeness_file = open(completeness_patterns_location + 'completeness-' + str(topic_files.index(topic)) + '.txt','r+')
	sort_by_metric(completeness_file,"completeness")
	completeness_file.close()


if __name__ == "__main__":
	if (len(sys.argv) == 2):
		min_support = float(sys.argv[1])
	print "Running Apriori Algorithm with min_support = " + str(min_support)
	if not os.path.exists(patterns_location):
			os.makedirs(patterns_location)
	if not os.path.exists(max_patterns_location):
			os.makedirs(max_patterns_location)
	if not os.path.exists(closed_patterns_location):
			os.makedirs(closed_patterns_location)
	if not os.path.exists(pure_patterns_location):
			os.makedirs(pure_patterns_location)
	if not os.path.exists(phraseness_patterns_location):
			os.makedirs(phraseness_patterns_location)
	if not os.path.exists(completeness_patterns_location):
			os.makedirs(completeness_patterns_location)
	vocab_map(vocab)
	D = make_D_matrix_for_purity()
	for topic in topic_files:
		apriori(topic)
		find_max_patterns(topic)
		find_closed_patterns(topic)
		print "\n"
	for topic in topic_files:
		find_purity(topic,D)
		find_phraseness(topic,D)
		find_completeness(topic)
		print "\n"
