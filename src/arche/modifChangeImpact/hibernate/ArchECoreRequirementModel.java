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

package arche.modifChangeImpact.hibernate;

/**
 * A (default) Hibernate-based implementation for the interface ArchERequirementModel
 * <p>
 * Basically, the requirements model consists of a set of scenarios targeted to
 * different quality attributes. External reasoning frameworks are expected to 
 * share the same requirements model, but* they will be interested in specific 
 * 'sub-sets' of scenarios (also called scenarios of interest)
 * <p>
 * This class implements how to save, restore or update things in the DB.
 * Also, it handles the access to scenarios pertaining to a particular reasoning 
 * framework (scenarios of interest)
 * 
 * @author Hyunwoo Kim, Andres Diaz-Pace
 */

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.hibernate.HibernateException;
import org.hibernate.Query;
import org.hibernate.Session;

import arche.modifChangeImpact.hibernate.vo.ArchEScenarioVO;
import arche.modifChangeImpact.hibernate.vo.ArchEVersionVO;

import edu.cmu.sei.arche.ArchEException;
import edu.cmu.sei.arche.external.data.ArchERequirementModel;
import edu.cmu.sei.arche.external.data.ArchEScenario;
import edu.cmu.sei.arche.external.data.ArchEVersion;
import edu.cmu.sei.arche.external.reasoningframework.ArchEReasoningFramework;

public class ArchECoreRequirementModel implements ArchERequirementModel {

	protected ArchEVersionVO currentVersion;
	protected List<ArchEScenario> scenarioVOs;
	
	public ArchECoreRequirementModel(ArchEVersionVO currentVersion) {
		this.scenarioVOs = new ArrayList<ArchEScenario>();
		this.currentVersion = (ArchEVersionVO)currentVersion;
		//System.out.println("--> Current version: "+currentVersion.getId());		
	}
	
	public boolean addScenario(ArchEScenario scenario) {
		return (scenarioVOs.add(scenario));
	}
	
	public ArchEVersion getCurrentVersion() {
		return (ArchEVersion)currentVersion;
	}	
	
	public void restore() throws ArchEException{
		try{
	    	// Restore scenarios of interest, i.e., scenarios specific to the given reasoning framework
	    	Query qScenarios  = ArchECoreDataProvider.getSessionFactory()
				.getCurrentSession().createQuery("from ArchEScenarioVO as sc where sc.version = ?");
//				.getCurrentSession().createQuery("from ArchEScenarioVO as sc where sc.version = ? and sc.reasoningFramework = ?");
			qScenarios.setInteger(0, currentVersion.getId());
//	    	qScenarios.setString(1, reasoningFramework.getID());    	
	    	List<ArchEScenario> results = qScenarios.list();			  
	    	scenarioVOs = results;
		}catch (HibernateException ex){
			throw new ArchEException(ex.getMessage(),ex.getCause());
		}
	}

	public void save() throws ArchEException{
		Session openSession = ArchECoreDataProvider.getSessionFactory().getCurrentSession();
		if(openSession != null && openSession.isConnected() && openSession.isOpen()){
			try{
				for(Iterator<ArchEScenario> itScen = scenarioVOs.iterator(); itScen.hasNext();) 
					openSession.saveOrUpdate(itScen.next());			

			}catch (HibernateException ex){
				throw new ArchEException(ex.getMessage(),ex.getCause());
			}			
		}		
	}

	public void saveAs(ArchEVersionVO newVersion) throws ArchEException{
		Session openSession = ArchECoreDataProvider.getSessionFactory().getCurrentSession();
		if(openSession != null && openSession.isConnected() && openSession.isOpen()){
			try{
				ArchEScenarioVO itemScen = null;
				for(Iterator<ArchEScenario> itScen = scenarioVOs.iterator(); itScen.hasNext();){
					itemScen = (ArchEScenarioVO)(itScen.next());
					itemScen.setVersion(newVersion);					
					openSession.save(itemScen);			
				}
				
			}catch (HibernateException ex){
				throw new ArchEException(ex.getMessage(),ex.getCause());
			}			
		}
	}
	
	public List<ArchEScenario> getScenariosByReasoningFramework(
				ArchEReasoningFramework reasoningFramework) {
		List<ArchEScenario> scenariosOfInterest = new ArrayList<ArchEScenario>();
		ArchEScenarioVO item = null;
		for(Iterator<ArchEScenario> it = scenarioVOs.iterator(); it.hasNext();){
			item = (ArchEScenarioVO)(it.next());
			String rfID = item.getReasoningFramework();
			if(rfID != null && rfID.equalsIgnoreCase(reasoningFramework.getID()))
				scenariosOfInterest.add((ArchEScenario)item);
		}
		
		return scenariosOfInterest;
	}

	public List<ArchEScenario> getScenarios() {
		return scenarioVOs;
	}
	
}
