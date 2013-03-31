/*
 * ArchE
 * Copyright (c) 2012 Carnegie Mellon University.
 * All Rights Reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following acknowledgments and disclaimers.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 *
 * 3. All advertising materials for third-party software mentioning features or
 * use of this software must display the following disclaimer:
 *
 * “Neither Carnegie Mellon University nor its Software Engineering Institute
 * have reviewed or endorsed this software”
 *
 * 4. The names “Carnegie Mellon University,” and/or “Software Engineering
 * Institute" shall not be used to endorse or promote products derived from
 * this software without prior written permission. For written permission,
 * please contact permission@sei.cmu.edu.
 *
 * 5. Redistributions of any form whatsoever must retain the following
 * acknowledgment:
 *
 * Copyright 2012 Carnegie Mellon University.
 *
 * This material is based upon work funded and supported by the United States
 * Department of Defense under Contract No. FA8721-05-C-0003 with Carnegie
 * Mellon University for the operation of the Software Engineering Institute, a
 * federally funded research and development center.
 *
 * NO WARRANTY
 *
 * THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE ENGINEERING INSTITUTE MATERIAL
 * IS FURNISHED ON AN “AS-IS” BASIS. CARNEGIE MELLON UNIVERSITY MAKES NO
 * WARRANTIES OF ANY KIND, EITHER EXPRESSED OR IMPLIED, AS TO ANY MATTER
 * INCLUDING, BUT NOT LIMITED TO, WARRANTY OF FITNESS FOR PURPOSE OR
 * MERCHANTABILITY, EXCLUSIVITY, OR RESULTS OBTAINED FROM USE OF THE MATERIAL.
 * CARNEGIE MELLON UNIVERSITY DOES NOT MAKE ANY WARRANTY OF ANY KIND WITH
 * RESPECT TO FREEDOM FROM PATENT, TRADEMARK, OR COPYRIGHT INFRINGEMENT.
 */

package arche.modifChangeImpact;

/**
 * A responsibility structure that handles responsibility dependencies for the 
 * modifiability reasoning framework
 * <p>
 * From the point of view of modifiability, each responsibility must be annotated with
 * a cost-of-change parameter. Likewise,  responsibility dependencies are annotated 
 * with parameters probability-incoming and probability-outgoing, in order to reflect 
 * the probability of rippling when the source or target responsibilities of the 
 * relation are affected by a change.
 * 
 * @author Hyunwoo Kim, Andres Diaz-Pace
 */

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.List;

import org.hibernate.HibernateException;
import org.hibernate.Query;
import org.hibernate.Session;

import arche.modifChangeImpact.hibernate.ArchECoreArchitecture;
import arche.modifChangeImpact.hibernate.ArchECoreDataProvider;
import arche.modifChangeImpact.hibernate.ArchECoreResponsibilityStructure;
import arche.modifChangeImpact.hibernate.dao.ArchEParameterDAO;
import arche.modifChangeImpact.hibernate.vo.ArchERelationVO;
import arche.modifChangeImpact.hibernate.vo.ArchEResponsibilityDependencyRelationVO;
import arche.modifChangeImpact.hibernate.vo.ArchEResponsibilityVO;
import arche.modifChangeImpact.hibernate.vo.ArchEVersionVO;


import edu.cmu.sei.arche.ArchEException;
import edu.cmu.sei.arche.external.data.ArchERelation;

public class ChangeImpactModifiabilityResponsibilityStructure 
												extends ArchECoreResponsibilityStructure {

	private static Hashtable<String,String> mappingsToTables = new Hashtable<String,String>();

	// Mapping of reasoning-framework specific relations to MySQL tables
	static { // These mappings should come from the rf-xml configuration file
		mappingsToTables.put(ModifChangeImpactReasoningFramework.PARAMETER_COST_OF_CHANGE, 
				"changeimpactmodifiabilityrf_p_costofchange");
		mappingsToTables.put(ModifChangeImpactReasoningFramework.PARAMETER_PROBABILITY_INCOMING, 
				"changeimpactmodifiabilityrf_p_probabilityincoming");
		mappingsToTables.put(ModifChangeImpactReasoningFramework.PARAMETER_PROBABILITY_OUTGOING, 
				"changeimpactmodifiabilityrf_p_probabilityoutgoing");
	}
	
	public static void setParameterToTableMapping(String parameterName, String tableName) {
		mappingsToTables.put(parameterName, tableName);
		return;
	}

	
	protected List<ArchEResponsibilityDependencyRelationVO> depVOs; // For dependency relations	
	
	public ChangeImpactModifiabilityResponsibilityStructure(ArchECoreArchitecture architecture) {
		super(architecture);
		this.depVOs = new ArrayList<ArchEResponsibilityDependencyRelationVO>();	
	}

	public void restore() throws ArchEException{
		super.restore();
		
		Session openSession = ArchECoreDataProvider.getSessionFactory().getCurrentSession();
		try{
	    	// Restore the dependency relations between responsibilities
	    	Query qdeps = openSession.createQuery("from ArchEResponsibilityDependencyRelationVO as rel where rel.version = ?");
	    	qdeps.setInteger(0, version.getId());
	    	depVOs = qdeps.list();	
	    	
	    	for (Iterator<ArchEResponsibilityDependencyRelationVO> itDeps = depVOs.iterator(); itDeps.hasNext();)
	    		this.restoreParametersForRelation(itDeps.next(), openSession);
	    	
		}catch (HibernateException ex){
			//ex.printStackTrace();
			throw new ArchEException(ex.getMessage(),ex.getCause());
		}
	}
	
	public void save() throws ArchEException{
		super.save();
		
		Session openSession = ArchECoreDataProvider.getSessionFactory().getCurrentSession();
		try{
			// Save or update the dependency relations
			ArchEResponsibilityDependencyRelationVO rel = null;
			for(Iterator<ArchEResponsibilityDependencyRelationVO> it=depVOs.iterator(); it.hasNext() ; ) {
				rel = it.next();				
				openSession.saveOrUpdate(rel);
				this.saveParametersForRelation(rel, openSession);
			}
			
			//this.deleteDanglingParameters(openSession, version);

//			System.out.println("SAVING CURRENT: "+version.getId());

		}catch (HibernateException ex){
			throw new ArchEException(ex.getMessage(),ex.getCause());
		}			
	}

	public void saveAs(ArchEVersionVO newVersion) throws ArchEException {
		super.saveAs(newVersion);

		Session openSession = ArchECoreDataProvider.getSessionFactory().getCurrentSession();
		
		try{
			// Create a copy of the existing dependency relations
			ArchEResponsibilityDependencyRelationVO itemDep = null;
			for(Iterator<ArchEResponsibilityDependencyRelationVO> it = depVOs.iterator(); it.hasNext();){
				itemDep = it.next();
				itemDep.setVersion(newVersion);
				openSession.save(itemDep);
				this.saveParametersForRelationAs(newVersion, itemDep, openSession);
			}

			//this.deleteDanglingParameters(openSession, newVersion);
			
//			System.out.println("SAVING A CANDIDATE AS: "+newVersion.getId());

		}catch (HibernateException ex){
			throw new ArchEException(ex.getMessage(),ex.getCause());
		}			
	}
	
//	// This is a hook method to delete any parameter whose factId doesn't
//	// correspond to any actual responsibility/relation
//	protected void deleteDanglingParameters(Session openSession, ArchEVersionVO version) {
//		
//		String costOfChange = ModifChangeImpactReasoningFramework.PARAMETER_COST_OF_CHANGE;
//		String tableName1 = (String)(mappingsToTables.get(costOfChange));
//		List list = Arrays.asList(rawRSVO.getResponsibilities().toArray());
//		ArchEParameterDAO.deleteParametersBySetOfResponsibilities(list, version, tableName1, openSession);
//
//		String probabilityIncoming = ModifChangeImpactReasoningFramework.PARAMETER_PROBABILITY_INCOMING;
//		String tableName2 = (String)(mappingsToTables.get(probabilityIncoming));
//		ArchEParameterDAO.deleteParametersBySetOfRelations(depVOs, version, tableName2, openSession);
//
//
//		String probabilityOutgoing = ModifChangeImpactReasoningFramework.PARAMETER_PROBABILITY_INCOMING;
//		String tableName3 = (String)(mappingsToTables.get(probabilityOutgoing));
//		ArchEParameterDAO.deleteParametersBySetOfRelations(depVOs, version, tableName3, openSession);
//		
//		// Repeat the process for any possible dangling parameter that needs to be deleted
//
//		return;
//	}

	
	public void delete() throws ArchEException{
		super.delete();
		
		Session openSession = ArchECoreDataProvider.getSessionFactory().getCurrentSession();
		try{
			// Delete the dependency relations
			ArchEResponsibilityDependencyRelationVO itemDep = null;
			for (Iterator<ArchEResponsibilityDependencyRelationVO> itDep = depVOs.iterator(); itDep.hasNext();) {
				itemDep = itDep.next();
				openSession.delete(itemDep);
				this.deleteParametersForRelation(itemDep, openSession);
			}

		}catch (HibernateException ex){
			throw new ArchEException(ex.getMessage(),ex.getCause());
		}			
	}
	
	public boolean addRelation(ArchERelation rel) {
		if(super.addRelation(rel))
			return true;
		
		// The specific case of responsibility dependencies
		if (rel instanceof ArchEResponsibilityDependencyRelationVO) {
			return (depVOs.add((ArchEResponsibilityDependencyRelationVO)rel));
		}
		return (false);
	}
	
	public boolean deleteRelation(ArchERelation rel) {
		boolean deleted = super.deleteRelation(rel);
		if (deleted)
			return (true);
		// The specific case of responsibility dependencies
		if (rel instanceof ArchEResponsibilityDependencyRelationVO)
			return (depVOs.remove(rel));
		return (false);
	}
	
	public List<ArchERelation> getRelations(String relationTypeVO) {
		List<ArchERelation>  results = super.getRelations(relationTypeVO);
		if(results != null)
			return results;
		
		// TODO: Review the type conversions below, maybe they can be programmed in a different way
		ArchERelation[] result = null;
		if (relationTypeVO.equals(ArchEResponsibilityDependencyRelationVO.class.getName())) {
			result = new ArchERelation[depVOs.size()];
			result = depVOs.toArray(result);
			return (Arrays.asList(result));
		}
		else
			return (null);
		
	}

	// This is a hook method that is expected to  be overridden by an  ArchECoreResponsibilityStructure
	// subclass in order to load specific properties for a responsibility
	protected void restoreParametersForResponsibility(ArchEResponsibilityVO responsibility,
			Session openSession) {		

		String costOfChange = ModifChangeImpactReasoningFramework.PARAMETER_COST_OF_CHANGE;
		String tableName = (String)(mappingsToTables.get(costOfChange));
		Double parameterValue = ArchEParameterDAO.findDoubleParameter(tableName, 
				responsibility, version, openSession);
		if (parameterValue != null) 
			responsibility.defineParameter(costOfChange, parameterValue);
		
		// Repeat the process for any parameter that needs to be loaded
		
		return;
	}
	
	// This is a hook method that is expected to  be overridden by an  ArchECoreResponsibilityStructure
	// subclass in order to save specific properties for a responsibility
	protected void saveParametersForResponsibility(ArchEResponsibilityVO responsibility, Session openSession) {
		
		String costOfChange = ModifChangeImpactReasoningFramework.PARAMETER_COST_OF_CHANGE;
		String tableName = (String)(mappingsToTables.get(costOfChange));
		if (responsibility.hasParameter(costOfChange)) {			
			try {
				Double value = responsibility.getDoubleParameter(costOfChange);
				ArchEParameterDAO.saveOrUpdateDoubleParameter(tableName, 
						value, responsibility, version, openSession);
			} catch (ArchEException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}

		// Repeat the process for any parameter that needs to be saved

		return;
	}

	protected void saveParametersForResponsibilityAs(ArchEVersionVO newVersion, ArchEResponsibilityVO responsibility, Session openSession) {
		
		String costOfChange = ModifChangeImpactReasoningFramework.PARAMETER_COST_OF_CHANGE;
		String tableName = (String)(mappingsToTables.get(costOfChange));
		if (responsibility.hasParameter(costOfChange)) {			
			try {
				Double value = responsibility.getDoubleParameter(costOfChange);
				ArchEParameterDAO.saveOrUpdateDoubleParameter(tableName, 
						value, responsibility, newVersion, openSession);
			} catch (ArchEException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}

		// Repeat the process for any parameter that needs to be saved

		return;
	}

	// This is a hook method that is expected to  be overridden by an  ArchECoreResponsibilityStructure
	// subclass in order to load specific properties for a relation
	protected void restoreParametersForRelation(ArchERelationVO relation, Session openSession) {

		String probabilityIncoming = ModifChangeImpactReasoningFramework.PARAMETER_PROBABILITY_INCOMING;
		String tableName1 = (String)(mappingsToTables.get(probabilityIncoming));
		Double parameterValue1 = ArchEParameterDAO.findDoubleParameter(tableName1, 
				relation, version, openSession);
		if (parameterValue1 != null) 
			relation.defineParameter(probabilityIncoming, parameterValue1);

		String probabilityOutgoing = ModifChangeImpactReasoningFramework.PARAMETER_PROBABILITY_OUTGOING;
		String tableName2 = (String)(mappingsToTables.get(probabilityOutgoing));
		Double parameterValue2 = ArchEParameterDAO.findDoubleParameter(tableName2, 
				relation, version, openSession);
		if (parameterValue2 != null) 
			relation.defineParameter(probabilityOutgoing, parameterValue2);

		// Repeat the process for any parameter that needs to be loaded

		return;
	}

	// This is a hook method that is expected to  be overridden by an  ArchECoreResponsibilityStructure
	// subclass in order to save specific properties for a relation
	protected void saveParametersForRelation(ArchERelationVO relation, Session openSession) {
		
		String probabilityIncoming = ModifChangeImpactReasoningFramework.PARAMETER_PROBABILITY_INCOMING;
		String tableName1 = (String)(mappingsToTables.get(probabilityIncoming));
		if (relation.hasParameter(probabilityIncoming)) {			
			try {
				double value1 = relation.getDoubleParameter(probabilityIncoming);
				ArchEParameterDAO.saveOrUpdateDoubleParameter(tableName1, 
						value1, relation, version, openSession);
			} catch (ArchEException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}

		String probabilityOutgoing = ModifChangeImpactReasoningFramework.PARAMETER_PROBABILITY_OUTGOING;
		String tableName2 = (String)(mappingsToTables.get(probabilityOutgoing));
		if (relation.hasParameter(probabilityOutgoing)) {			
			try {
				double value2 = relation.getDoubleParameter(probabilityOutgoing);
				ArchEParameterDAO.saveOrUpdateDoubleParameter(tableName2, 
						value2, relation, version, openSession);
			} catch (ArchEException e) { 
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}

		// Repeat the process for any parameter that needs to be saved
		
		return;
	}

	protected void saveParametersForRelationAs(ArchEVersionVO newVersion, ArchERelationVO relation, Session openSession) {
		
		String probabilityIncoming = ModifChangeImpactReasoningFramework.PARAMETER_PROBABILITY_INCOMING;
		String tableName1 = (String)(mappingsToTables.get(probabilityIncoming));
		if (relation.hasParameter(probabilityIncoming)) {			
			try {
				double value1 = relation.getDoubleParameter(probabilityIncoming);
				ArchEParameterDAO.saveOrUpdateDoubleParameter(tableName1, 
						value1, relation, newVersion, openSession);
			} catch (ArchEException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}

		String probabilityOutgoing = ModifChangeImpactReasoningFramework.PARAMETER_PROBABILITY_OUTGOING;
		String tableName2 = (String)(mappingsToTables.get(probabilityOutgoing));
		if (relation.hasParameter(probabilityOutgoing)) {			
			try {
				double value2 = relation.getDoubleParameter(probabilityOutgoing);
				ArchEParameterDAO.saveOrUpdateDoubleParameter(tableName2, 
						value2, relation, newVersion, openSession);
			} catch (ArchEException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}

		// Repeat the process for any parameter that needs to be saved
		
		return;
	}
	
	// This is a hook method that is expected to  be overridden by an  ArchECoreResponsibilityStructure
	// subclass in order to delete specific properties for a responsibility
	protected void deleteParametersForResponsibility(ArchEResponsibilityVO responsibility, Session openSession) {

		String costOfChange = ModifChangeImpactReasoningFramework.PARAMETER_COST_OF_CHANGE;
		String tableName = (String)(mappingsToTables.get(costOfChange));
		if (responsibility.hasParameter(costOfChange)) 			
			ArchEParameterDAO.deleteParameter(costOfChange, tableName, responsibility, version, openSession);

		// Repeat the process for any parameter that needs to be deleted

		return;
	}

	// This is a hook method that is expected to  be overridden by an  ArchECoreResponsibilityStructure
	// subclass in order to delete specific properties for a relationship
	protected void deleteParametersForRelation(ArchERelationVO relation, Session openSession) {

		String probabilityIncoming = ModifChangeImpactReasoningFramework.PARAMETER_PROBABILITY_INCOMING;
		String tableName1 = (String)(mappingsToTables.get(probabilityIncoming));
		if (relation.hasParameter(probabilityIncoming)) 			
			ArchEParameterDAO.deleteParameter(probabilityIncoming, tableName1, relation, version, openSession);

		String probabilityOutgoing = ModifChangeImpactReasoningFramework.PARAMETER_PROBABILITY_OUTGOING;
		String tableName2 = (String)(mappingsToTables.get(probabilityOutgoing));
		if (relation.hasParameter(probabilityOutgoing))	
			ArchEParameterDAO.deleteParameter(probabilityOutgoing, tableName2, relation, version, openSession);

		// Repeat the process for any parameter that needs to be deleted
		
		return;
	}
	
}
